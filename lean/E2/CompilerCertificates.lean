import E2.RawWords

/-! Quantitative evaluation of finite two-sided algebraic certificates.
The right word pays its state commutator cost; no trace hypothesis is used. -/
namespace E2.CompilerCertificates
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Companion.Analytic

@[simp] theorem weighted_zero {d : ℕ} (s : State d) : weighted s (0 : Mat d) = 0 := by
  simp [weighted, hs, hsNorm, hsSquared]

open scoped Matrix.Norms.Frobenius in
theorem hs_smul {d : ℕ} (z : ℂ) (A : Mat d) :
    hs (z • A) = ‖z‖ * hs A := by
  simpa only [hs, hsNorm_eq_frobenius] using norm_smul z A

theorem weighted_smul {d : ℕ} (s : State d) (z : ℂ) (A : Mat d) :
    weighted s (z • A) = ‖z‖ * weighted s A := by
  unfold weighted
  rw [Matrix.smul_mul]
  exact hs_smul z (A * s.xi)

theorem weighted_list_sum {d : ℕ} (s : State d) (xs : List (Mat d)) :
    weighted s xs.sum ≤ (xs.map (weighted s)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simpa only [List.sum_cons, List.map_cons] using (weighted_add s a xs.sum).trans
      (add_le_add_right ih (weighted s a))

/-- A single two-sided word multiple. The bound depends on the right word's
length and the relation's operator norm, not on the dimension or state. -/
theorem word_multiple_bound {d : ℕ} (s : State d) (hd : 0 < d)
    (η B : ℝ) (hη : 0 ≤ η) (hB : 0 ≤ B) (R : Mat d)
    (hR : weighted s R ≤ η) (hRn : ‖R‖ ≤ B)
    (left right : List (Mat d))
    (hnl : ∀ A ∈ left, ‖A‖ ≤ 1) (hnr : ∀ A ∈ right, ‖A‖ ≤ 1)
    (hcr : ∀ A ∈ right, hs (comm A s.xi) ≤ η) :
    weighted s (left.prod * R * right.prod) ≤ (1 + B * right.length) * η := by
  have hc := word_state_commutator s hd η hη right hnr hcr
  have hn := word_norm hd right hnr
  have hl := word_norm hd left hnl
  calc
    _ = weighted s (left.prod * (R * right.prod)) := by rw [Matrix.mul_assoc]
    _ ≤ ‖left.prod‖ * weighted s (R * right.prod) := weighted_left s _ _
    _ ≤ weighted s (R * right.prod) := by
      exact (mul_le_mul_of_nonneg_right hl (hsNorm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖right.prod‖ * weighted s R + ‖R‖ * hs (comm right.prod s.xi) :=
      weighted_right s _ _
    _ ≤ 1 * η + B * (right.length * η) := by
      gcongr <;> exact hsNorm_nonneg _
    _ = (1 + B * right.length) * η := by ring

/-- Evaluated finite certificate. `identity` is the concrete algebraic equality
that must be established for each compiler gadget; it is not an admitted rule. -/
theorem finite_certificate_bound {d n : ℕ} (s : State d) (hd : 0 < d)
    (η : ℝ) (hη : 0 ≤ η)
    (coefficient : Fin n → ℂ) (relation : Fin n → Mat d)
    (left right : Fin n → List (Mat d)) (B : Fin n → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hR : ∀ i, weighted s (relation i) ≤ η)
    (hRn : ∀ i, ‖relation i‖ ≤ B i)
    (hnl : ∀ i A, A ∈ left i → ‖A‖ ≤ 1)
    (hnr : ∀ i A, A ∈ right i → ‖A‖ ≤ 1)
    (hcr : ∀ i A, A ∈ right i → hs (comm A s.xi) ≤ η)
    (target : Mat d)
    (identity : target = ∑ i, coefficient i • ((left i).prod * relation i * (right i).prod)) :
    weighted s target ≤
      (∑ i, ‖coefficient i‖ * (1 + B i * (right i).length)) * η := by
  rw [identity, Finset.sum_mul]
  classical
  have hsum (t : Finset (Fin n)) :
      weighted s (∑ i ∈ t, coefficient i • ((left i).prod * relation i * (right i).prod)) ≤
      ∑ i ∈ t, (‖coefficient i‖ * (1 + B i * (right i).length)) * η := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      calc
        _ ≤ weighted s (coefficient i • ((left i).prod * relation i * (right i).prod)) +
              weighted s (∑ j ∈ t, coefficient j • ((left j).prod * relation j * (right j).prod)) :=
          weighted_add s _ _
        _ ≤ (‖coefficient i‖ * (1 + B i * (right i).length)) * η +
              ∑ j ∈ t, (‖coefficient j‖ * (1 + B j * (right j).length)) * η := by
          apply add_le_add _ ih
          rw [weighted_smul]
          simpa only [mul_assoc, Matrix.mul_assoc] using mul_le_mul_of_nonneg_left
            (word_multiple_bound s hd η (B i) hη (hB i) (relation i) (hR i) (hRn i)
              (left i) (right i) (hnl i) (hnr i) (hcr i)) (norm_nonneg (coefficient i))
  simpa using hsum Finset.univ

end
end E2.CompilerCertificates
