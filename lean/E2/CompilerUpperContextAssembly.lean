import E2.CompilerUpperMeasurements

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerStrategy
variable {V : Type*} [Fintype V] [Nonempty V] {d : ℕ}

/-- Pushing outcomes into total labels preserves every marginal. -/
theorem outcomes_marginal {G : BCSGame}
    (k : Fin G.contexts → ℕ) (M : (c : Fin G.contexts) → Fin (k c) → Mat d)
    (label : (c : Fin G.contexts) → Fin (k c) → (Fin G.numVars → Bool))
    (hM : ∀ c i, Domain.projection.Holds (M c i))
    (hmul : ∀ c i j, M c i*M c j=if i=j then M c i else 0)
    (hsum : ∀ c, ∑ i, M c i=1) (hlegal : ∀ c i, label c i ∈ G.allowed c) (c) (v) :
    (ContextPVM.ofOutcomes k M label hM hmul hsum hlegal).marginal c v=
      ∑ i, if label c i v then M c i else 0 := by
  classical
  unfold ContextPVM.marginal ContextPVM.ofOutcomes
  have ht (a : Fin G.numVars → Bool) :
      (if a v then ∑ i, if label c i=a then M c i else 0 else 0)=
      ∑ i, if label c i=a then (if label c i v then M c i else 0) else 0 := by
    by_cases h : a v=true
    · simp only [h,↓reduceIte]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : label c i=a <;> simp [hi,h]
    · simp only [h,Bool.false_eq_true,↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : label c i=a <;> simp [hi,h]
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The game's extra singleton context has its exact Bob marginal. -/
theorem extra_measurement (X : V → Mat d) (hX : ∀ v, Domain.reflection.Holds (X v)) :
    ∃ A : TableMeasurement (free ({0} : Finset (Fin (Fintype.card V)))) d,
      A.marginal 0=decodeProjection (X ((Fintype.equivFin V).symm 0)) := by
  classical
  obtain ⟨A,hA⟩ := free_measurement ({0}:Finset (Fin (Fintype.card V)))
    (fun v => X ((Fintype.equivFin V).symm v)) (fun v _ => hX _)
    (by intro v hv w hw; simp only [Finset.mem_singleton] at hv hw; subst v; subst w; exact Commute.refl _)
  exact ⟨A,hA 0 (by simp)⟩

/-- Assemble local table PVMs, including relabeling and the extra free context,
into the unchanged game's ContextPVM with all total assignment labels. -/
theorem table_measurements_contexts (ts : List (Table V))
    (X : V → Mat d) (hX : ∀ v, Domain.reflection.Holds (X v))
    (A : (i : Fin ts.length) → TableMeasurement (ts.get i) d) :
    ∃ B : ContextPVM (game ts) d,
      B.marginal (0 : Fin (ts.length+1)) (0 : Fin (Fintype.card V))=decodeProjection (X ((Fintype.equivFin V).symm 0)) ∧
      ∀ (i : Fin ts.length) (v : V), B.marginal i.succ (Fintype.equivFin V v)=(A i).marginal v := by
  classical
  obtain ⟨extra,hextra⟩ := extra_measurement X hX
  let T : Fin (ts.length+1) → Table (Fin (Fintype.card V)) :=
    Fin.cases (free {0}) (fun i => (ts.get i).relabel)
  let C : (c : Fin (ts.length+1)) → TableMeasurement (T c) d :=
    Fin.cases extra (fun i => (A i).relabel)
  let k := fun c => (C c).outcomes
  let M := fun c => (C c).value
  let label := fun c => (C c).label
  have hlegal (c i) : label c i ∈ (game ts).allowed c := by
    change label c i ∈ Finset.univ.filter (T c).accepts
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (C c).legal i
  let B : ContextPVM (game ts) d := ContextPVM.ofOutcomes k M label
    (fun c => (C c).domains) (fun c => (C c).multiply) (fun c => (C c).complete) hlegal
  have hm (c v) : B.marginal c v=(C c).marginal v :=
    outcomes_marginal k M label _ _ _ hlegal c v
  refine ⟨B,?_,?_⟩
  · rw [hm]
    exact hextra
  · intro i v
    rw [hm]
    exact (A i).relabel_marginal v

end
end E2.CompilerUpper
