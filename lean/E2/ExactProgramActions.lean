import E2.ExactResetModel

namespace E2.ExactForcing
noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem action_mul (x y Q : A) (a b : ℂ) (hx : x*Q=a • Q) (hy : y*Q=b • Q) :
    x*y*Q=(a*b) • Q := by
  rw [mul_assoc,hy,mul_smul_comm,hx,smul_smul,mul_comm b a]

theorem action_sub_one (x Q : A) (a : ℂ) (hx : x*Q=a • Q) :
    (1-x)*Q=(1-a) • Q := by rw [sub_mul,one_mul,hx,sub_smul,one_smul]

theorem action_smul (x Q : A) (a b : ℂ) (hx : x*Q=a • Q) :
    (b • x)*Q=(b*a) • Q := by rw [smul_mul_assoc,hx,smul_smul]

theorem eval_psum {ι : Type*} (x : ι → A) (rs : List (Poly ι)) :
    (psum rs).evalC x=(rs.map (Poly.evalC x)).sum := by
  induction rs with
  | nil => simp [psum]
  | cons r rs ih => simpa only [psum,List.foldr_cons,Poly.evalC_add,List.map_cons,List.sum_cons] using congrArg (fun y => r.evalC x+y) ih

theorem sum_finRange {B : Type*} [AddCommMonoid B] (n : ℕ) (f : Fin n → B) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem sum_flatMap {B C : Type*} [AddMonoid B] (xs : List C) (f : C → List B) :
    (xs.flatMap f).sum=(xs.map (fun c => (f c).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

def counterTerm (p : CounterProgram) (x : SourceVar p → A) (i : Fin p.counters) (q : Fin p.controls) : A :=
  match p.instruction q with
  | .inc j _ => (sq p q).evalC x * ((if i=j then 1/2 else 1:ℂ) • (sr p i).evalC x)
  | .dec j _ _ => (sq p q).evalC x*(sz p j).evalC x*(sr p i).evalC x +
      (sq p q).evalC x*(1-(sz p j).evalC x)*((if i=j then 2 else 1:ℂ) • (sr p i).evalC x)
  | .jump _ => (sq p q).evalC x*(sr p i).evalC x
  | .stay => (sq p q).evalC x*(sr p i).evalC x

def controlTerm (p : CounterProgram) (x : SourceVar p → A) (i q : Fin p.controls) : A :=
  match p.instruction q with
  | .inc _ q' => if q'=i then (sq p q).evalC x else 0
  | .dec j q₀ q₁ => (if q₀=i then (sq p q).evalC x*(sz p j).evalC x else 0) +
      (if q₁=i then (sq p q).evalC x*(1-(sz p j).evalC x) else 0)
  | .jump q' => if q'=i then (sq p q).evalC x else 0
  | .stay => if q=i then (sq p q).evalC x else 0

theorem eval_nextCounter (p : CounterProgram) (x : SourceVar p → A) (i : Fin p.counters) :
    (nextCounter p i).evalC x=∑ q, counterTerm p x i q := by
  rw [nextCounter,eval_psum,programBranches,List.map_flatMap,List.map_flatMap,sum_flatMap]
  rw [←sum_finRange]
  congr 1
  apply List.map_congr_left
  intro q hq
  cases h : p.instruction q <;>
    simp [counterTerm,h,Poly.evalC_sub,smul_mul_assoc,one_mul,mul_smul_comm,mul_assoc]
  all_goals split_ifs <;> norm_num

theorem eval_nextControl (p : CounterProgram) (x : SourceVar p → A) (i : Fin p.controls) :
    (nextControl p i).evalC x=∑ q, controlTerm p x i q := by
  rw [nextControl,eval_psum,programBranches,List.map_flatMap,List.map_flatMap,sum_flatMap]
  rw [←sum_finRange]
  congr 1
  apply List.map_congr_left
  intro q hq
  cases h : p.instruction q <;> simp [controlTerm,h]
  all_goals split_ifs <;> simp

def counterCode (n : ℕ) : ℂ := (2:ℂ)^(-(n:ℤ))

theorem counterCode_zero : counterCode 0=1 := by simp [counterCode]

theorem counterCode_succ (n : ℕ) : counterCode (n+1)=(1/2:ℂ)*counterCode n := by
  simp only [counterCode,Nat.cast_add,Nat.cast_one,neg_add_rev,zpow_add₀ (by norm_num : (2:ℂ)≠0)]
  norm_num

theorem counterCode_pred (n : ℕ) (hn : n≠0) : counterCode (n-1)=2*counterCode n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.succ_sub_one,counterCode_succ]
  ring

theorem counterTerm_inactive (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (i : Fin p.counters) (q : Fin p.controls)
    (hr : ∀ j, (sr p j).evalC x*Q=counterCode (c.counter j) • Q)
    (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : (sq p q).evalC x*Q=0) : counterTerm p x i q*Q=0 := by
  cases h : p.instruction q <;>
    simp [counterTerm,h,add_mul,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hz,sub_mul,hq]

theorem counterTerm_active (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (i : Fin p.counters)
    (hr : ∀ j, (sr p j).evalC x*Q=counterCode (c.counter j) • Q)
    (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : (sq p c.control).evalC x*Q=Q) :
    counterTerm p x i c.control*Q=counterCode ((p.step c).counter i) • Q := by
  cases h : p.instruction c.control with
  | inc j q =>
    simp only [counterTerm,h,CounterProgram.step,Function.update_apply]
    by_cases hij : i=j
    · subst i
      simp [mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hq,counterCode_succ]
    · simp [hij,Ne.symm hij,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hq]
  | dec j q₀ q₁ =>
    by_cases hn : c.counter j=0
    · simp [counterTerm,h,CounterProgram.step,hn,add_mul,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hz,sub_mul,hq]
    · by_cases hij : i=j
      · subst i
        simp [counterTerm,h,CounterProgram.step,hn,add_mul,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hz,sub_mul,hq,counterCode_pred _ hn]
      · simp [counterTerm,h,CounterProgram.step,hn,hij,Ne.symm hij,add_mul,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hz,sub_mul,hq]
  | jump q => simp [counterTerm,h,CounterProgram.step,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hq]
  | stay => simp [counterTerm,h,CounterProgram.step,mul_assoc,mul_smul_comm,smul_smul,mul_sub,hr,hq]

theorem nextCounter_action (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (hr : ∀ j, (sr p j).evalC x*Q=counterCode (c.counter j) • Q)
    (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : ∀ q, (sq p q).evalC x*Q=if q=c.control then Q else 0) (i : Fin p.counters) :
    (nextCounter p i).evalC x*Q=counterCode ((p.step c).counter i) • Q := by
  rw [eval_nextCounter,Finset.sum_mul]
  rw [Finset.sum_eq_single c.control]
  · exact counterTerm_active p x c Q i hr hz (by simpa using hq c.control)
  · intro q hqmem hne
    exact counterTerm_inactive p x c Q i q hr hz (by simpa [hne] using hq q)
  · simp

theorem controlTerm_inactive (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (i q : Fin p.controls)
    (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : (sq p q).evalC x*Q=0) : controlTerm p x i q*Q=0 := by
  cases h : p.instruction q <;>
    simp [controlTerm,h,add_mul,mul_assoc,mul_sub,hz,sub_mul,hq]

theorem controlTerm_active (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (i : Fin p.controls)
    (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : (sq p c.control).evalC x*Q=Q) :
    controlTerm p x i c.control*Q=if i=(p.step c).control then Q else 0 := by
  cases h : p.instruction c.control <;>
    simp [controlTerm,h,CounterProgram.step,add_mul,mul_assoc,mul_sub,hz,sub_mul,hq,eq_comm]
  all_goals split_ifs <;> simp_all

theorem nextControl_action (p : CounterProgram) (x : SourceVar p → A) (c : Configuration p)
    (Q : A) (hz : ∀ j, (sz p j).evalC x*Q=if c.counter j=0 then Q else 0)
    (hq : ∀ q, (sq p q).evalC x*Q=if q=c.control then Q else 0) (i : Fin p.controls) :
    (nextControl p i).evalC x*Q=if i=(p.step c).control then Q else 0 := by
  rw [eval_nextControl,Finset.sum_mul]
  rw [Finset.sum_eq_single c.control]
  · exact controlTerm_active p x c Q i hz (by simpa using hq c.control)
  · intro q hqmem hne
    exact controlTerm_inactive p x c Q i q hz (by simpa [hne] using hq q)
  · simp

end
end E2.ExactForcing
