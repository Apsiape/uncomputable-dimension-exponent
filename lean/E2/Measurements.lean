import E2.MeasurementDefs
import E2.CountInformation

namespace E2
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

/-- Theorem 8.1. C is absolute; every operator condition and state is explicit. -/
theorem triangular_measurement_count : ∃ C : ℝ, 0 < C ∧
    ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d) (u : Fin m → Mat d),
    0 < d → 0 ≤ η → TriangularRelations s η p u → C*m^4*η^2 ≤ 1/2 →
    Real.logb 2 d ≥ binaryCount p + activeSum s p - C*m^3*η -
      m*(binaryEntropy (C*m^4*η^2) + C*m^4*η^2) := by
  exact triangular_measurement_count_proof

end
end E2
