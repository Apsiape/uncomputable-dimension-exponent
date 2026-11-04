import E2.Game
import E2.StateConsistencyRectangular
import Mathlib.Tactic

namespace E2.BooleanGameLoss
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
variable {G : BCSGame} {d : ℕ}

def outcome (s : Strategy G d) (c : Fin G.contexts) (v : Fin G.numVars)
    (a : Fin G.numVars → Bool) (b : Bool) : ℝ :=
  (Matrix.trace (s.rho * Matrix.kronecker (s.alice c a) (s.bob v b))).re

theorem outcome_nonneg (s : Strategy G d) (c v a b) : 0 ≤ outcome s c v a b :=
  FiniteTransfer.generic_psd_trace _ _ s.rho_positive
    ((s.alice_positive c a).kronecker (s.bob_positive v b))

theorem outcome_sum (s : Strategy G d) (c v) : (∑ a, ∑ b, outcome s c v a b) = 1 := by
  have hm : (∑ a, ∑ b, Matrix.kronecker (s.alice c a) (s.bob v b)) = 1 := by
    calc
      _ = Matrix.kronecker (∑ a, s.alice c a) (∑ b, s.bob v b) := by
        ext i j
        simp [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.mul_sum,Finset.sum_mul,mul_add,Finset.sum_add_distrib]
      _ = 1 := by
        rw [s.alice_complete,s.bob_complete]
        exact Matrix.one_kronecker_one
  have hc : (∑ a, ∑ b, Matrix.trace (s.rho * Matrix.kronecker (s.alice c a) (s.bob v b))) = 1 := by
    calc
      _ = Matrix.trace (s.rho * (∑ a, ∑ b, Matrix.kronecker (s.alice c a) (s.bob v b))) := by
        simp only [Matrix.mul_sum,Matrix.trace_sum]
      _ = 1 := by rw [hm,Matrix.mul_one,s.rho_trace]
  simpa only [outcome,Complex.re_sum,Complex.one_re] using congrArg Complex.re hc

def localLoss (s : Strategy G d) (c : Fin G.contexts) (v : Fin G.numVars) : ℝ :=
  1 - ∑ a ∈ G.allowed c, outcome s c v a (a v)

theorem localLoss_nonneg (s : Strategy G d) (c v) : 0 ≤ localLoss s c v := by
  have hsub : (∑ a ∈ G.allowed c, outcome s c v a (a v)) ≤ ∑ a, ∑ b, outcome s c v a b := by
    calc
      _ ≤ ∑ a ∈ G.allowed c, ∑ b, outcome s c v a b := by
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.single_le_sum (fun b hb => outcome_nonneg s c v a b) (Finset.mem_univ (a v))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a ha hnot =>
        Finset.sum_nonneg (fun b hb => outcome_nonneg s c v a b))
  rw [outcome_sum] at hsub
  exact sub_nonneg.mpr hsub

theorem loss_eq_sum (s : Strategy G d) :
    loss s = ∑ c, ∑ v, (G.probability c v : ℝ) * localLoss s c v := by
  have hp : (∑ c, ∑ v, (G.probability c v : ℝ)) = 1 := by exact_mod_cast G.probability_sum
  simp only [localLoss,mul_sub,mul_one,Finset.sum_sub_distrib]
  rw [hp]
  rfl

def lossConstant (G : BCSGame) : ℝ :=
  1 + ∑ c, ∑ v, if v ∈ G.scope c then (G.probability c v : ℝ)⁻¹ else 0

theorem lossConstant_pos (G : BCSGame) : 0 < lossConstant G := by
  have hh : 0 ≤ ∑ c, ∑ v, if v ∈ G.scope c then (G.probability c v : ℝ)⁻¹ else 0 := by
    apply Finset.sum_nonneg
    intro c hc
    apply Finset.sum_nonneg
    intro v hv
    split_ifs
    · exact inv_nonneg.mpr (by exact_mod_cast G.probability_nonneg c v)
    · exact le_rfl
  unfold lossConstant
  linarith

/-- Every tested incidence has a dimension-independent error bound. -/
theorem localLoss_bound (s : Strategy G d) (ε : ℝ) (hε : 0 ≤ ε) (hs : loss s ≤ ε)
    (c v) (hv : v ∈ G.scope c) : localLoss s c v ≤ lossConstant G * ε := by
  have hpq : 0 < G.probability c v := lt_of_le_of_ne (G.probability_nonneg c v)
    (Ne.symm ((G.probability_support c v).mpr hv))
  have hp : 0 < (G.probability c v : ℝ) := by exact_mod_cast hpq
  have he : (G.probability c v : ℝ) * localLoss s c v ≤ ε := by
    apply le_trans ?_ hs
    rw [loss_eq_sum]
    calc
      _ ≤ ∑ w, (G.probability c w : ℝ) * localLoss s c w :=
        Finset.single_le_sum (fun w hw => mul_nonneg
          (by exact_mod_cast G.probability_nonneg c w) (localLoss_nonneg s c w)) (Finset.mem_univ v)
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun e => ∑ w, (G.probability e w : ℝ) * localLoss s e w)
          (fun e he => Finset.sum_nonneg (fun w hw =>
            mul_nonneg (by exact_mod_cast G.probability_nonneg e w) (localLoss_nonneg s e w)))
          (Finset.mem_univ c)
  have hi : (G.probability c v : ℝ)⁻¹ ≤ lossConstant G := by
    have ha := Finset.single_le_sum (fun w hw => show
      0 ≤ if w ∈ G.scope c then (G.probability c w : ℝ)⁻¹ else 0 by
        split_ifs; exact inv_nonneg.mpr (by exact_mod_cast G.probability_nonneg c w); exact le_rfl)
      (Finset.mem_univ v)
    have hb := Finset.single_le_sum (f := fun e => ∑ w, if w ∈ G.scope e then (G.probability e w : ℝ)⁻¹ else 0)
      (fun e he => Finset.sum_nonneg (fun w hw => show
      0 ≤ if w ∈ G.scope e then (G.probability e w : ℝ)⁻¹ else 0 by
        split_ifs; exact inv_nonneg.mpr (by exact_mod_cast G.probability_nonneg e w); exact le_rfl))
      (Finset.mem_univ c)
    simp only [hv,ite_true] at ha
    unfold lossConstant
    linarith
  calc
    _ ≤ (G.probability c v : ℝ)⁻¹ * ε := by
      have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
      simpa only [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hp),one_mul] using hh
    _ ≤ _ := mul_le_mul_of_nonneg_right hi hε

end
end E2.BooleanGameLoss
