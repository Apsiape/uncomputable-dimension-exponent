import E2.CompilerCertificates

/-! Ordered Boolean assignment expansions. None of the partition identities
requires commuting operators, so they apply before approximate commutation repair. -/
namespace E2.CompilerBoolean
noncomputable section
open scoped BigOperators

def splitAssignment (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun a := (a 0, fun i => a i.succ)
  invFun a := Fin.cons a.1 a.2
  left_inv a := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv a := by cases a; simp

theorem sum_assignments_succ {A : Type*} [AddCommMonoid A] {n : ℕ}
    (f : (Fin (n+1) → Bool) → A) :
    ∑ a, f a = ∑ b : Bool, ∑ a : Fin n → Bool, f (Fin.cons b a) := by
  calc
    _ = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      Fintype.sum_equiv (splitAssignment n) _ _ (fun a => (congrArg f ((splitAssignment n).left_inv a)).symm)
    _ = _ := Fintype.sum_prod_type _

def ordered {A : Type*} [Monoid A] {n : ℕ} (f : Fin n → A) : A := (List.ofFn f).prod

@[simp] theorem ordered_zero {A : Type*} [Monoid A] (f : Fin 0 → A) : ordered f = 1 := by
  simp [ordered]

@[simp] theorem ordered_succ {A : Type*} [Monoid A] {n : ℕ} (f : Fin (n+1) → A) :
    ordered f = f 0 * ordered (fun i => f i.succ) := by
  simp [ordered, List.ofFn_succ]

/-- Noncommutative distributivity, in the fixed variable order. -/
theorem assignment_expansion {A : Type*} [Semiring A] {n : ℕ}
    (f : Fin n → Bool → A) :
    ∑ a : Fin n → Bool, ordered (fun i => f i (a i)) =
      ordered (fun i => f i true + f i false) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_assignments_succ]
    simp only [ordered_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih]
    rw [Fintype.sum_bool, add_mul]

variable {d : ℕ}

def atom (x : Mat d) (b : Bool) : Mat d :=
  if b then (1/2 : ℂ) • (1+x) else (1/2 : ℂ) • (1-x)

@[simp] theorem atom_partition (x : Mat d) : atom x true + atom x false = 1 := by
  simp only [atom, ↓reduceIte, Bool.false_eq_true]
  module

@[simp] theorem atom_difference (x : Mat d) : atom x true - atom x false = x := by
  simp only [atom, ↓reduceIte, Bool.false_eq_true]
  module

def joint {n : ℕ} (x : Fin n → Mat d) (a : Fin n → Bool) : Mat d :=
  ordered (fun i => atom (x i) (a i))

/-- Exact partition of unity even for noncommuting reflections. -/
theorem joint_partition {n : ℕ} (x : Fin n → Mat d) : ∑ a, joint x a = 1 := by
  unfold joint
  rw [assignment_expansion]
  simp only [atom_partition]
  simp [ordered]

/-- A Boolean truth table is a finite linear combination of its assignment
polynomials. This estimate uses only the forbidden assignments. -/
theorem forbidden_table_bound {n : ℕ} (s : State d) (x : Fin n → Mat d)
    (allowed : Finset (Fin n → Bool)) (coefficient : (Fin n → Bool) → ℂ)
    (η : ℝ) (_hη : 0 ≤ η)
    (hzero : ∀ a ∈ allowed, coefficient a = 0)
    (hdef : ∀ a, a ∉ allowed → weighted s (joint x a) ≤ η) :
    weighted s (∑ a, coefficient a • joint x a) ≤ (∑ a, ‖coefficient a‖) * η := by
  classical
  have hs (t : Finset (Fin n → Bool)) :
      weighted s (∑ a ∈ t, coefficient a • joint x a) ≤ ∑ a ∈ t, ‖coefficient a‖ * η := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      apply (weighted_add s _ _).trans
      apply add_le_add _ ih
      by_cases h : a ∈ allowed
      · simp [hzero a h]
      · rw [CompilerCertificates.weighted_smul]
        exact mul_le_mul_of_nonneg_left (hdef a h) (norm_nonneg _)
  simpa only [Finset.mem_univ, Finset.sum_const_zero, Finset.sum_mul] using hs Finset.univ

end
end E2.CompilerBoolean
