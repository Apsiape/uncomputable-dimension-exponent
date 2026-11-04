import E2.ExactProgramModel

namespace E2.ExactForcing
noncomputable section
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

def homPower (f : A →⋆ₐ[ℂ] A) : ℕ → A →⋆ₐ[ℂ] A
  | 0 => StarAlgHom.id ℂ A
  | n+1 => f.comp (homPower f n)

theorem homPower_zero (f : A →⋆ₐ[ℂ] A) (x : A) : homPower f 0 x=x := rfl

theorem homPower_succ (f : A →⋆ₐ[ℂ] A) (n : ℕ) (x : A) :
    homPower f (n+1) x=f (homPower f n x) := rfl

theorem homPower_succ' (f : A →⋆ₐ[ℂ] A) (n : ℕ) (x : A) :
    homPower f (n+1) x=homPower f n (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [homPower_succ f (n+1) x,ih,homPower_succ f n (f x)]

theorem transition_action (z ini nxt Q : A) (a b : ℂ)
    (hz : z*Q=0) (hi : ini*Q=a • Q) (hn : nxt*Q=b • Q) :
    (z*ini+(1-z)*nxt)*Q=b • Q := by
  simp only [add_mul,mul_assoc,hi,hn,mul_smul_comm,sub_mul,one_mul,hz,
    smul_zero,zero_add,sub_zero]

theorem initialize_action (Z w ini Q : A) (a : ℂ)
    (hZ : Z*Q=Q) (hcomm : Commute Z w) (heq : Z*w=Z*ini) (hi : ini*Q=a • Q) :
    w*Q=a • Q := by
  calc
    w*Q=w*(Z*Q) := by rw [hZ]
    _=(Z*w)*Q := by rw [←mul_assoc,hcomm.eq]
    _=(Z*ini)*Q := by rw [heq]
    _=a • Q := by rw [mul_assoc,hi,mul_smul_comm,hZ]

theorem initialCounter_action (p : CounterProgram) (x : SourceVar p → A) (e : ℕ) (Q : A)
    (hL : (sv p 16).evalC x*Q=counterCode e • Q) (i : Fin p.counters) :
    (initialCounter p i).evalC x*Q=counterCode ((p.initial e).counter i) • Q := by
  simp only [initialCounter,CounterProgram.initial]
  split_ifs
  · exact hL
  · simp [counterCode_zero]

theorem initialControl_action (p : CounterProgram) (x : SourceVar p → A) (Q : A)
    (hH : (sv p 15).evalC x*Q=Q) (i : Fin p.controls) :
    (initialControl p i).evalC x*Q=if i=p.start then Q else 0 := by
  simp only [initialControl]
  split_ifs <;> simp_all [sub_mul]

theorem finite_program_iteration {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (e h : ℕ) (Q : A)
    (hZ : sourceValue m 17*Q=Q)
    (hno : ∀ l, 0<l → l≤h → homPower (timeStep m) l (sourceValue m 17)*Q=0)
    (hH : ∀ l, l≤h → homPower (timeStep m) l (sourceValue m 15)*Q=Q)
    (hL : ∀ l, l≤h → homPower (timeStep m) l (sourceValue m 16)*Q=counterCode e • Q) :
    ∀ l, l≤h →
      (∀ i, homPower (timeStep m) l ((sr p i).evalC m.value)*Q=
        counterCode (((p.step)^[l] (p.initial e)).counter i) • Q) ∧
      (∀ q, homPower (timeStep m) l ((sq p q).evalC m.value)*Q=
        if q=((p.step)^[l] (p.initial e)).control then Q else 0) := by
  have hIniR (l : ℕ) (hl : l≤h) (i : Fin p.counters) :
      homPower (timeStep m) l ((initialCounter p i).evalC m.value)*Q=
        counterCode ((p.initial e).counter i) • Q := by
    rw [←ExactTrace.eval_map]
    apply initialCounter_action
    simpa only [ExactTrace.eval_map,sv,Poly.evalC_var,sourceValue] using hL l hl
  have hIniQ (l : ℕ) (hl : l≤h) (i : Fin p.controls) :
      homPower (timeStep m) l ((initialControl p i).evalC m.value)*Q=
        (if i=p.start then (1:ℂ) else 0) • Q := by
    rw [←ExactTrace.eval_map]
    have hi := initialControl_action p (fun j => homPower (timeStep m) l (m.value j)) Q
      (by simpa only [ExactTrace.eval_map,sv,Poly.evalC_var,sourceValue] using hH l hl) i
    split_ifs at hi ⊢ <;> simpa using hi
  intro l
  induction l with
  | zero =>
    intro hl
    constructor
    · intro i
      simp only [homPower_zero,Function.iterate_zero,Function.id_def]
      exact initialize_action _ _ _ Q _ hZ
        (workspace_comm m (sv p 17) (sr p i) (by simp) (List.mem_cons_of_mem _ (sr_mem_work p i)))
        (counter_updates m i).1 (hIniR 0 hl i)
    · intro q
      have hi := initialize_action _ _ _ Q _ hZ
        (workspace_comm m (sv p 17) (sq p q) (by simp) (List.mem_cons_of_mem _ (sq_mem_work p q)))
        (control_updates m q).1 (hIniQ 0 hl q)
      simp only [homPower_zero,Function.iterate_zero,Function.id_def,
        CounterProgram.initial,ite_smul,one_smul,zero_smul] at hi ⊢
      convert hi using 1 <;> rfl
  | succ l ih =>
    intro hl
    have hle : l≤h := by omega
    obtain ⟨hr,hq⟩ := ih hle
    let f := homPower (timeStep m) l
    let c := (p.step)^[l] (p.initial e)
    have hz := model_zero_test m f Q c hr
    have hr' (i : Fin p.counters) :
        (sr p i).evalC (fun j => f (m.value j))*Q=counterCode (c.counter i) • Q := by
      simpa only [ExactTrace.eval_map] using hr i
    have hz' (i : Fin p.counters) :
        (sz p i).evalC (fun j => f (m.value j))*Q=if c.counter i=0 then Q else 0 := by
      simpa only [ExactTrace.eval_map] using hz i
    have hq' (q : Fin p.controls) :
        (sq p q).evalC (fun j => f (m.value j))*Q=if q=c.control then Q else 0 := by
      simpa only [ExactTrace.eval_map] using hq q
    have hzero : f (timeStep m (sourceValue m 17))*Q=0 := by
      rw [←homPower_succ']
      exact hno (l+1) (by omega) hl
    constructor
    · intro i
      rw [homPower_succ',(counter_updates m i).2,map_add,map_mul,map_mul,map_sub,map_one]
      have hn := nextCounter_action p (fun j => f (m.value j)) c Q hr' hz' hq' i
      rw [ExactTrace.eval_map] at hn
      simpa only [Function.iterate_succ_apply',c] using
        transition_action _ _ _ Q _ _ hzero (hIniR l hle i) hn
    · intro q
      rw [homPower_succ',(control_updates m q).2,map_add,map_mul,map_mul,map_sub,map_one]
      have hn := nextControl_action p (fun j => f (m.value j)) c Q hz' hq' q
      rw [ExactTrace.eval_map] at hn
      by_cases hqc : q=(p.step c).control
      · simp only [hqc,ite_true] at hn
        have ha := transition_action _ _ _ Q _ 1 hzero (hIniQ l hle q) (by simpa using hn)
        simpa only [Function.iterate_succ_apply',c,hqc,ite_true,one_smul] using ha
      · simp only [hqc,ite_false] at hn
        have ha := transition_action _ _ _ Q _ 0 hzero (hIniQ l hle q) (by simpa using hn)
        simpa only [Function.iterate_succ_apply',c,hqc,ite_false,zero_smul] using ha

end
end E2.ExactForcing
