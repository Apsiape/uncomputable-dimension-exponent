import E2.MeasurementDefs

namespace E2.Recording
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

/-- The stacked recording map has exactly the Gram matrix of its Kraus family. -/
theorem stack_gram {ι : Type*} [Fintype ι] {d : ℕ} (A : ι → Mat d) :
    (stack A).conjTranspose * stack A = ∑ i, (A i).conjTranspose * A i := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stack,
    Fintype.sum_prod_type, Matrix.sum_apply]


/-- Completeness gives an operator bound independent of the number of branches. -/
theorem stack_norm_le_one {ι : Type*} [Fintype ι] {d : ℕ} (A : ι → Mat d)
    (hA : ∑ i, (A i).conjTranspose * A i = 1) : ‖stack A‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (stack A)
  rw [stack_gram, hA] at h
  have h1 : ‖(1 : Mat d)‖ ≤ 1 := by
    by_cases hd : d=0
    · subst d
      have hz : (1 : Mat 0)=0 := Subsingleton.elim _ _
      rw [hz,norm_zero]; norm_num
    · letI : NeZero d := ⟨hd⟩
      simp
  nlinarith [norm_nonneg (stack A)]

theorem stack_sub {ι : Type*} {d : ℕ} (A B : ι → Mat d) :
    stack (fun i => A i - B i) = stack A - stack B := rfl

theorem difference_column_norm {ι : Type*} [Fintype ι] {d : ℕ} (A B : ι → Mat d)
    (hA : ∑ i, (A i).conjTranspose * A i = 1)
    (hB : ∑ i, (B i).conjTranspose * B i = 1) :
    ‖stack (fun i => A i - B i)‖ ≤ 2 := by
  rw [stack_sub]
  exact (norm_sub_le _ _).trans (by linarith [stack_norm_le_one A hA, stack_norm_le_one B hB])

/-- Both orders of two PVM recordings are isometries, even if they do not commute. -/
theorem composition_complete {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (P : ι → Mat d) (Q : κ → Mat d)
    (hP : ∑ a, (P a).conjTranspose * P a = 1)
    (hQ : ∑ b, (Q b).conjTranspose * Q b = 1) :
    (∑ t : ι × κ, (P t.1 * Q t.2).conjTranspose * (P t.1 * Q t.2)) = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have he (b : κ) :
      (∑ a, (Q b).conjTranspose * ((P a).conjTranspose * (P a * Q b))) =
        (Q b).conjTranspose * Q b := by
    calc
      _ = (Q b).conjTranspose * (∑ a, (P a).conjTranspose * P a) * Q b := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  simp_rw [he]
  exact hQ

theorem commutator_column_norm {ι κ : Type*} [Fintype ι] [Fintype κ] {d : ℕ}
    (P : ι → Mat d) (Q : κ → Mat d)
    (hP : ∑ a, (P a).conjTranspose * P a = 1)
    (hQ : ∑ b, (Q b).conjTranspose * Q b = 1) :
    ‖stack (fun t : ι × κ => comm (P t.1) (Q t.2))‖ ≤ 2 := by
  apply difference_column_norm _ _ (composition_complete P Q hP hQ)
  have h := composition_complete Q P hQ hP
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simpa only [Fintype.sum_prod_type] using h

/-- A pair of at-most-three-outcome measurements contributes at most 3 eta
in family norm, independently of prefix branch probabilities. -/
theorem pair_commutator_error {d : ℕ} (s : State d) (η : ℝ) (P Q : Measurement d)
    (hη : 0 ≤ η)
    (h : ∀ a b, weighted s (comm (P.projection a) (Q.projection b)) ≤ η) :
    familyNorm (fun t : Fin P.outcomes × Fin Q.outcomes =>
      comm (P.projection t.1) (Q.projection t.2) * s.xi) ≤ 3 * η := by
  have hP : P.outcomes ≤ 3 := by rcases P.arity with h | h <;> omega
  have hQ : Q.outcomes ≤ 3 := by rcases Q.arity with h | h <;> omega
  apply (sq_le_sq₀ (familyNorm_nonneg _) (by positivity : 0 ≤ 3 * η)).mp
  rw [familyNorm_sq]
  calc
    _ ≤ ∑ _t : Fin P.outcomes × Fin Q.outcomes, η ^ 2 :=
      Finset.sum_le_sum (fun t _ => pow_le_pow_left₀ (hsNorm_nonneg _) (h t.1 t.2) 2)
    _ = (P.outcomes : ℝ) * Q.outcomes * η ^ 2 := by simp
    _ ≤ (3 * η) ^ 2 := by
      have hPQ : (P.outcomes : ℝ) * Q.outcomes ≤ 9 := by
        exact_mod_cast (show P.outcomes * Q.outcomes ≤ 9 by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_right hPQ (sq_nonneg η)]

/-- The elementary adjacent swap after ANY measurement prefix. The estimate
uses the original mixed-state square root and sums all prefix branches. -/
theorem adjacent_swap_after_prefix {d m : ℕ} (s : State d) (η : ℝ)
    (pre : Fin m → Measurement d) (P Q : Measurement d) (hη : 0 ≤ η)
    (hstate : ∀ i a, hs (comm ((pre i).projection a) s.xi) ≤ η)
    (hcomm : ∀ a b, weighted s (comm (P.projection a) (Q.projection b)) ≤ η) :
    familyNorm (fun r : RecordType pre =>
      stack (fun t : Fin P.outcomes × Fin Q.outcomes =>
        comm (P.projection t.1) (Q.projection t.2)) * recordingWord pre r * s.xi) ≤
      3 * η + 2 * m * Real.sqrt 3 * η := by
  simp only [recordingWord, ← List.ofFn_eq_map]
  apply recorded_column_bound (fun i => (pre i).projection)
    (fun i => by simpa only [(pre i).selfadjoint, (pre i).idempotent] using (pre i).complete)
    (fun i => by simpa only [(pre i).selfadjoint, (pre i).idempotent] using (pre i).complete)
    (fun i => by rcases (pre i).arity with h | h <;> omega)
    s.xi _ η (3 * η) 2 hη (by norm_num) hstate
  · apply commutator_column_norm
    · simpa only [P.selfadjoint, P.idempotent] using P.complete
    · simpa only [Q.selfadjoint, Q.idempotent] using Q.complete
  · change familyNorm (fun t : Fin P.outcomes × Fin Q.outcomes =>
        comm (P.projection t.1) (Q.projection t.2) * s.xi) ≤ _
    exact pair_commutator_error s η P Q hη hcomm

end
end E2.Recording


