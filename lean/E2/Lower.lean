import E2.Measurements
import E2.Tracial
import E2.Joint
import E2.LowerAnalytic

namespace E2
noncomputable section

/-- A uniform little-o lower estimate, expanded into its full epsilon-delta
quantifiers over every state and dimension. -/
def UniformLower {ι : Type*} (P : Presentation ι) (slope : ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (δ : ℝ) (d : ℕ) (_m : Model P d δ), 0 < δ → δ < δ₀ →
      (slope-γ)*Real.logb 4 (1/δ) ≤ Real.logb 2 d

/-- Theorem 9.1: asymptotic depth selection and counting after Lemma 9.3.
The compactness, measurement-count, and joint-family inputs are explicit.
This analytic assembly is itself an outstanding proof, not an external premise. -/
theorem lower_from_measurements (p : CounterProgram)
    (flag : ∃ ω : ℝ → ℝ,
      Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (δ : ℝ) (d : ℕ) (m : Model (sourcePresentation p) d δ), 0 < δ →
        thetaK-ω δ ≤ expectation m.state (modelValue m 18))
    (count : ∃ C : ℝ, 0 < C ∧
      ∀ (d m : ℕ) (s : State d) (η : ℝ) (P : Fin m → Measurement d) (u : Fin m → Mat d),
      0 < d → 0 ≤ η → TriangularRelations s η P u → C*m^4*η^2 ≤ 1/2 →
      Real.logb 2 d ≥ binaryCount P + activeSum s P - C*m^3*η -
        m*(binaryEntropy (C*m^4*η^2)+C*m^4*η^2))
    (joint : ∃ C : ℝ, 0 < C ∧ ∀ (d M : ℕ) (δ : ℝ)
      (m : Model (sourcePresentation p) d δ), 1 ≤ M → 0 ≤ δ → Nonempty (JointFamily m M C)) :
    UniformLower (sourcePresentation p) (3+thetaK) := by
  obtain ⟨ω,hω,hflag⟩ := flag
  obtain ⟨C,hC,hcount⟩ := count
  obtain ⟨K,hK,hjoint⟩ := joint
  exact uniform_lower_analytic p ω hω hflag C K hC hK hcount hjoint

theorem arbitrary_state_lower (p : CounterProgram) (hp : RecognizesK p) :
    UniformLower (sourcePresentation p) (3+thetaK) := by
  apply lower_from_measurements p
  · exact uniform_flag_density p hp
  · exact triangular_measurement_count
  · obtain ⟨C,hC,h⟩ := joint_measurements
    exact ⟨C,hC,fun d M δ m hM hδ => h p d M δ m hM hδ⟩

end
end E2

