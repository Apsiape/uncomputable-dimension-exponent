import E2.Transfer
import E2.EffectiveDyadic
import E2.EffectiveApproximation
import E2.EffectiveNoncomputable
import E2.EffectiveOracle
import E2.HaltingDegree

namespace E2
noncomputable section

/-- Lemma 2.4, fixed-positive-rational precision. Natural numbers code
rationals, avoiding any assumed computability structure on the reals. -/
theorem fixed_precision_computable (hT : RealArithmetic.TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    Computable (fun n : ℕ => if 0 < rationalCode n then
      (dimension G (rationalCode n)).toNat else 0) := by
  exact FeasibilityComputation.fixed_precision hT G hG

theorem dyadic_slope_computable (hT : RealArithmetic.TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    ComputableRealSequence (dyadicSlope G) := by
  exact EffectiveDyadic.dyadic_sequence hT G hG

/-- Second assertion of Lemma 2.4. The eventual threshold may be hardcoded. -/
theorem certified_rate_computes_limit (a : ℕ → ℝ) (β : ℝ)
    (ha : ComputableRealSequence a) (hr : CertifiedRate a β) : ComputableReal β := by
  exact EffectiveApproximation.certified_limit a β ha hr

/-- Section 10: both reductions, using the separated base-four digits of K. -/
theorem theta_halting_degree : TuringEquivalent (realOracle thetaK) haltingOracle := by
  exact HaltingDegree.theta_equivalent

theorem exponent_halting_degree : ExponentHasHaltingDegree := by
  exact TuringEquivalent.trans _ _ _ (EffectiveOracle.affine_equivalent thetaK) theta_halting_degree

theorem exponent_not_computable : ¬ ComputableReal betaK := by
  exact EffectiveNoncomputable.beta_not_computable

theorem no_certified_rate (hT : RealArithmetic.TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    ¬ CertifiedRate (dyadicSlope G) betaK := by
  intro hr
  exact exponent_not_computable
    (certified_rate_computes_limit _ _ (dyadic_slope_computable hT G hG) hr)

end
end E2
