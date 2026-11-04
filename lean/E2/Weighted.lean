import E2.Presentation
import Mathlib.Tactic

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

def column {d n : ℕ} (a : Matrix (Fin d) (Fin n) ℂ) (j : Fin n) :
    EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun i => a i j)

theorem hs_sq_columns {d n : ℕ} (a : Matrix (Fin d) (Fin n) ℂ) :
    hs a ^ 2 = ∑ j, ‖column a j‖ ^ 2 := by
  simp only [hsNorm_sq, hsSquared, column, EuclideanSpace.norm_sq_eq,
    Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

/-- Ported from Companion.Analytic.ReturnProof.operator_mul_hs_bound,
with the column-space calculation made local to avoid its entropy imports. -/
theorem operator_mul_hs {d n : ℕ} (c : Mat d) (a : Matrix (Fin d) (Fin n) ℂ) :
    hs (c * a) ≤ ‖c‖ * hs a := by
  have hcol (j : Fin n) : column (c * a) j =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) c (column a j) := by
    ext i
    rfl
  have hj (j : Fin n) : ‖column (c * a) j‖ ≤ ‖c‖ * ‖column a j‖ := by
    rw [hcol, Matrix.cstar_norm_def]
    exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) c).le_opNorm _
  have hsq : hs (c * a) ^ 2 ≤ (‖c‖ * hs a) ^ 2 := by
    rw [hs_sq_columns]
    calc
      _ ≤ ∑ j, (‖c‖ * ‖column a j‖) ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2)
      _ = ‖c‖ ^ 2 * (∑ j, ‖column a j‖ ^ 2) := by simp only [mul_pow, Finset.mul_sum]
      _ = (‖c‖ * hs a) ^ 2 := by rw [← hs_sq_columns]; ring
  exact (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (norm_nonneg _) (hsNorm_nonneg _))).mp hsq

theorem hs_mul_operator {d n : ℕ} (a : Matrix (Fin n) (Fin d) ℂ) (c : Mat d) :
    hs (a * c) ≤ hs a * ‖c‖ := by
  change hsNorm (a * c) ≤ hsNorm a * ‖c‖
  rw [← hsNorm_conjTranspose (a * c), Matrix.conjTranspose_mul]
  have h := operator_mul_hs c.conjTranspose a.conjTranspose
  simpa only [hsNorm_conjTranspose, ← Matrix.star_eq_conjTranspose, norm_star, mul_comm] using h

theorem hs_sub_le {d n : ℕ} (a b : Matrix (Fin d) (Fin n) ℂ) :
    hs (a - b) ≤ hs a + hs b := by
  rw [sub_eq_add_neg]
  have hn : hs (-b) = hs b := by
    simp only [hs, hsNorm, hsSquared, Matrix.neg_apply, Complex.normSq_neg]
  calc
    _ ≤ hs a + hs (-b) := hsNorm_add_le _ _
    _ = _ := by rw [hn]

/-- Lemma 2.2, left multiplication. -/
theorem weighted_left {d : ℕ} (s : State d) (a b : Mat d) :
    weighted s (a * b) ≤ ‖a‖ * weighted s b := by
  simpa only [weighted, Matrix.mul_assoc] using operator_mul_hs a (b * s.xi)

/-- Lemma 2.2, right multiplication, with its actual state commutator cost. -/
theorem weighted_right {d : ℕ} (s : State d) (a b : Mat d) :
    weighted s (b * a) ≤ ‖a‖ * weighted s b + ‖b‖ * hs (comm a s.xi) := by
  have he : b * a * s.xi = (b * s.xi) * a + b * comm a s.xi := by
    simp only [comm, Companion.Analytic.comm, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  unfold weighted
  rw [he]
  calc
    _ ≤ hs ((b * s.xi) * a) + hs (b * comm a s.xi) := hsNorm_add_le _ _
    _ ≤ hs (b * s.xi) * ‖a‖ + ‖b‖ * hs (comm a s.xi) :=
      add_le_add (hs_mul_operator _ _) (operator_mul_hs _ _)
    _ = _ := by ring

/-- Equation (9.7): replacing a self-adjoint correction in a commutator
adds its weighted error. This is one of the safeguards against two depth losses.
The proof actually works without self-adjointness. -/
theorem commutator_replace {d : ℕ} (s : State d) (D Y : Mat d) (hY : ‖Y‖ ≤ 1) :
    weighted s (comm D Y) ≤ 2 * weighted s D + ‖D‖ * hs (comm Y s.xi) := by
  have hw : 0 ≤ weighted s D := hsNorm_nonneg _
  calc
    _ ≤ weighted s (D * Y) + weighted s (Y * D) := by
      simpa only [weighted, comm, Companion.Analytic.comm, Matrix.sub_mul] using hs_sub_le ((D * Y) * s.xi) ((Y * D) * s.xi)
    _ ≤ (‖Y‖ * weighted s D + ‖D‖ * hs (comm Y s.xi)) +
          ‖Y‖ * weighted s D := add_le_add (weighted_right s Y D) (weighted_left s Y D)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hY hw]

/-- The additive replacement identity used across different compulsory clocks. -/
theorem commutator_two_replacements {d : ℕ} (x y dx dy : Mat d) :
    comm (x + dx) (y + dy) = comm dx (y + dy) + comm x dy + comm x y := by
  simp only [comm, Companion.Analytic.comm, Matrix.add_mul, Matrix.mul_add]
  abel

/-- Scalar bookkeeping in Lemma 9.2: a uniform one-step loss accumulates
linearly, rather than by repeatedly applying a Lipschitz constant to old error. -/
theorem linear_accumulation (e : ℕ → ℝ) (C δ : ℝ) (h0 : e 0 = 0)
    (hstep : ∀ i, e (i + 1) ≤ e i + C * δ) : ∀ i, e i ≤ i * C * δ := by
  intro i
  induction i with
  | zero => simp [h0]
  | succ i ih =>
    calc
      e (i + 1) ≤ e i + C * δ := hstep i
      _ ≤ i * C * δ + C * δ := add_le_add ih (le_refl _)
      _ = (i + 1 : ℕ) * C * δ := by push_cast; ring

end
end E2
