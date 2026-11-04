import E2.BooleanExtractionPVM
import E2.BooleanStrategyDilation
import E2.BooleanGameLoss
import E2.BooleanMixedAmplitude

namespace E2.BooleanExtraction
noncomputable section
open scoped Matrix.Norms.L2Operator
open E2.CompilerStrategy

/-- Primitive projective/consistency data still to be constructed from the
original strategy. This contains no Model and no polynomial-defect premise. -/
structure ConsistencyWitness (G : BCSGame) (c d : ℕ) (η : ℝ) where
  localDimension : ℕ
  dimension_bound : localDimension ≤ c*d
  referenceDimension : ℕ
  reference_pos : 0 < referenceDimension
  state : State localDimension
  amplitude : Matrix (Fin localDimension) (Fin referenceDimension) ℂ
  marginal : state.rho = amplitude * amplitude.conjTranspose
  bob : Fin G.numVars → Mat localDimension
  bob_reflections : ∀ v, Domain.reflection.Holds (bob v)
  alice : ContextPVM G referenceDimension
  consistency : ∀ c v, v ∈ G.scope c →
    hs (bob v * amplitude - amplitude * contextValue alice c v) ≤ η
  unused : ∀ v, (∀ c, v ∉ G.scope c) → bob v = 1

/-- Exact remaining construction obligation; a proposition, not a theorem,
axiom, admission, or external hypothesis. -/
def StrategyConsistencyBridge (G : BCSGame) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
    ∀ (ε : ℝ) (d : ℕ) (s : Strategy G d), 0 ≤ ε → loss s ≤ ε →
      Nonempty (ConsistencyWitness G c d (K * Real.sqrt ε))

/-- Every field after the missing bridge is now proved, including the
state commutators and every forbidden assignment in the original statement. -/
theorem ConsistencyWitness.model {G : BCSGame} {c d : ℕ} {η : ℝ}
    (w : ConsistencyWitness G c d η) (hη : 0 ≤ η) :
    Nonempty (Model (booleanPresentation G) w.localDimension (extractionConstant G * η)) :=
  model_of_pvm_consistency w.reference_pos w.state w.amplitude w.marginal w.bob
    w.bob_reflections w.alice η hη w.consistency w.unused

end
end E2.BooleanExtraction
