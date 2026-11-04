import E2.FiniteBitClock
import Mathlib.Analysis.SpecificLimits.Normed

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def boundedSeries (f : ℕ → ℝ) : ℝ := ∑' j, coefficient j*f j

theorem coefficient_hasSum : HasSum coefficient 1 := by
  have h := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)| < 1)).mul_left (3/4)
  convert h using 1
  · funext j
    simp only [coefficient,pow_succ]
    ring
  · norm_num

theorem boundedSeries_summable (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    Summable (fun j => coefficient j*f j) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (coefficient_nonneg j) (hf j).1)
    (fun j => ?_) coefficient_hasSum.summable
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf j).2 (coefficient_nonneg j)

theorem boundedSeries_bounds (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ boundedSeries f ∧ boundedSeries f ≤ 1 := by
  constructor
  · exact tsum_nonneg (fun j => mul_nonneg (coefficient_nonneg j) (hf j).1)
  · rw [boundedSeries,←coefficient_hasSum.tsum_eq]
    exact (boundedSeries_summable f hf).tsum_le_tsum
      (fun j => by simpa using mul_le_mul_of_nonneg_left (hf j).2 (coefficient_nonneg j))
      coefficient_hasSum.summable

theorem boundedSeries_shift (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1) :
    boundedSeries f = (3/4:ℝ)*f 0 + (1/4:ℝ)*boundedSeries (fun j => f (j+1)) := by
  rw [boundedSeries,(boundedSeries_summable f hf).tsum_eq_zero_add]
  norm_num only [coefficient,pow_one]
  congr 1
  rw [boundedSeries,←tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [coefficient,pow_succ]
  ring

/-- Agreement on a prefix controls the full, simultaneous infinite tail.
This scalar estimate is stronger than a triangle bound on separate matrices. -/
theorem boundedSeries_prefix (f g : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ 1)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ 1) (N : ℕ) (he : ∀ j < N, f j=g j) :
    |boundedSeries f-boundedSeries g| ≤ (1/4:ℝ)^N := by
  induction N generalizing f g with
  | zero =>
    have hfb := boundedSeries_bounds f hf
    have hgb := boundedSeries_bounds g hg
    norm_num only [pow_zero]
    exact abs_le.mpr ⟨by linarith [hfb.1,hgb.2],by linarith [hfb.2,hgb.1]⟩
  | succ N ih =>
    have htail := ih (fun j => f (j+1)) (fun j => g (j+1))
      (fun j => hf (j+1)) (fun j => hg (j+1)) (fun j hj => he (j+1) (by omega))
    rw [boundedSeries_shift f hf,boundedSeries_shift g hg,he 0 (by omega)]
    have heq : (3/4:ℝ)*g 0+1/4*boundedSeries (fun j => f (j+1))-
        (3/4*g 0+1/4*boundedSeries (fun j => g (j+1))) =
        (1/4:ℝ)*(boundedSeries (fun j => f (j+1))-boundedSeries (fun j => g (j+1))) := by ring
    rw [heq,abs_mul]
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/4)]
    rw [pow_succ]
    nlinarith

def permutationSeries {α : Type*} (s : Equiv.Perm α) (q : α → ℝ) (x : α) : ℝ :=
  boundedSeries (fun j => q ((s^j) x))

theorem permutationSeries_bounds {α : Type*} (s : Equiv.Perm α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (x : α) :
    0 ≤ permutationSeries s q x ∧ permutationSeries s q x ≤ 1 :=
  boundedSeries_bounds _ (fun j => hq _)

theorem permutationSeries_affine {α : Type*} (s : Equiv.Perm α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (x : α) :
    permutationSeries s q (s x) = 4*permutationSeries s q x-3*q x := by
  have h := boundedSeries_shift (fun j => q ((s^j) x)) (fun j => hq _)
  have he : (fun j => q ((s^(j+1)) x)) = (fun j => q ((s^j) (s x))) := by
    funext j
    rw [pow_succ,Equiv.Perm.mul_apply]
  rw [he] at h
  simp only [pow_zero,Equiv.Perm.one_apply] at h
  change permutationSeries s q x = (3/4:ℝ)*q x+(1/4:ℝ)*permutationSeries s q (s x) at h
  linarith

theorem permutationSeries_prefix {α : Type*} (s : Equiv.Perm α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (N : ℕ) (x y : α)
    (he : ∀ j, 1 ≤ j → j ≤ N → q ((s^j) x)=q ((s^j) y)) :
    |permutationSeries s q (s x)-permutationSeries s q (s y)| ≤ (1/4:ℝ)^N := by
  apply boundedSeries_prefix _ _ (fun j => hq _) (fun j => hq _) N
  intro j hj
  simpa only [pow_succ,Equiv.Perm.mul_apply] using he (j+1) (by omega) (by omega)

/-- Actual operator-norm control of the tail commutator for diagonal series. -/
theorem permutationSeries_commutator {α : Type*} [Fintype α] [DecidableEq α]
    (s y : Equiv.Perm α) (q : α → ℝ) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) (N : ℕ)
    (he : ∀ x j, 1 ≤ j → j ≤ N → q ((s^j) (y x))=q ((s^j) x)) :
    ‖y.permMatrix ℂ*Matrix.diagonal (fun x => (permutationSeries s q (s x):ℂ))-
      Matrix.diagonal (fun x => (permutationSeries s q (s x):ℂ))*y.permMatrix ℂ‖ ≤ (1/4:ℝ)^N := by
  apply perm_comm_diagonal_norm _ _ _ (by positivity)
  intro x
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact permutationSeries_prefix s q hq N (y x) x (he x)

end
end E2.FiniteConstruction