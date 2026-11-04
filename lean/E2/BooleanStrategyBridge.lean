import E2.BooleanExtractionBridge
import E2.BooleanConsistencyEstimate

namespace E2.BooleanExtraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Companion.Analytic E2.CompilerStrategy
open BooleanBridgeData BooleanGameLoss BooleanRealignment BooleanMixedAmplitude

 theorem strategy_dimension_pos {G : BCSGame} {d : ℕ} (s : Strategy G d) : 0 < d := by
  by_contra h
  have hd : d=0 := by omega
  subst d
  have ht := s.rho_trace
  simp [Matrix.trace] at ht

/-- The original arbitrary POVM/mixed-state strategy supplies the primitive
consistency witness, with Bob dimension at most three times the input. -/
theorem strategyConsistencyBridge (G : BCSGame) : StrategyConsistencyBridge G := by
  classical
  refine ⟨3,by omega,2 * Real.sqrt (lossConstant G),
    mul_pos (by norm_num) (Real.sqrt_pos.mpr (lossConstant_pos G)),?_⟩
  intro ε d s hε hloss
  have hd := strategy_dimension_pos s
  have hb : 0 < bdim d := by unfold bdim; rw [BooleanStrategyDilation.bob_dimension]; omega
  have ha : 0 < adim G d := by unfold adim; rw [BooleanStrategyDilation.alice_dimension]; positivity
  have href : 0 < refSize (adim G d) (bdim d) := by
    simp only [refSize,Reference,Fintype.card_prod,Fintype.card_fin]
    positivity
  let B : Fin G.numVars → Mat (bdim d) :=
    fun v => if ∃ c, v ∈ G.scope c then reflection s v else 1
  have hB : ∀ v, Domain.reflection.Holds (B v) := by
    intro v
    dsimp only [B]
    split_ifs
    · exact reflection_domain s v
    · constructor <;> simp
  have hbound (c) (v) (hv : v ∈ G.scope c) :
      hs (B v * amplitude (BooleanBridgeData.rho s) - amplitude (BooleanBridgeData.rho s) *
        contextValue (referencePVM (d := bdim d) (legalPVM s)) c v) ≤
        (2 * Real.sqrt (lossConstant G)) * Real.sqrt ε := by
    have he : B v = reflection s v := if_pos ⟨c,hv⟩
    rw [he]
    have ht := (consistency_bound_sq s c v).trans
      (mul_le_mul_of_nonneg_left (localLoss_bound s ε hε hloss c v hv) (by norm_num : (0:ℝ) ≤ 4))
    apply (sq_le_sq₀ (hsNorm_nonneg _) (by positivity :
      0 ≤ (2 * Real.sqrt (lossConstant G)) * Real.sqrt ε)).mp
    calc
      _ ≤ 4 * (lossConstant G * ε) := ht
      _ = ((2 * Real.sqrt (lossConstant G)) * Real.sqrt ε)^2 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (le_of_lt (lossConstant_pos G)),Real.sq_sqrt hε]
        ring
  exact ⟨{
    localDimension := bdim d
    dimension_bound := by unfold bdim; rw [BooleanStrategyDilation.bob_dimension]
    referenceDimension := refSize (adim G d) (bdim d)
    reference_pos := href
    state := marginalState (BooleanBridgeData.rho s) (BooleanBridgeData.rho_positive s)
      (BooleanBridgeData.rho_trace s)
    amplitude := amplitude (BooleanBridgeData.rho s)
    marginal := amplitude_gram _ _ _
    bob := B
    bob_reflections := hB
    alice := referencePVM (legalPVM s)
    consistency := hbound
    unused := by
      intro v hv
      dsimp only [B]
      rw [if_neg (by simpa only [not_exists] using hv)]
  }⟩

end
end E2.BooleanExtraction
