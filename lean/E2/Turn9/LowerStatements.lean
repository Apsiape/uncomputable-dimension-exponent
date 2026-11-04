import E2.Tracial
import E2.JointAccounting

/-! Section 9 proof specifications; these are not assumed results. -/
namespace E2.Turn9
noncomputable section
open scoped BigOperators

def depth (t : ℝ) : ℕ := ⌊t-30*Real.logb 4 (2+t)⌋₊
def countPenalty (C : ℝ) (M : ℕ) (η : ℝ) : ℝ :=
  C*(4*M)^3*η + (4*M)*(binaryEntropy (C*(4*M)^4*η^2)+C*(4*M)^4*η^2)

/-- Planned lemma: depth_asymptotics. The exact floor in equation (9.11). -/
def DepthAsymptotics : Prop :=
  Filter.Tendsto (fun t : ℝ => (depth t : ℝ)/t) Filter.atTop (nhds 1) ∧
  ∀ C K : ℝ, 0 < C → 0 < K →
    Filter.Tendsto (fun t : ℝ => countPenalty C (depth t)
      (jointError (depth t) ((4:ℝ)^(-t)) K)) Filter.atTop (nhds 0)

/-- Planned lemma: flag_translate_expectation, without flatness. -/
def FlagTranslateExpectation : Prop :=
  ∀ (d : ℕ) (s : State d) (V F : Mat d) (δ : ℝ),
  Domain.unitary.Holds V → Domain.projection.Holds F →
  hs (comm V s.xi) ≤ δ →
  ∀ i : ℕ, |expectation s (translate V F i) - expectation s F| ≤ 2*i*δ

/-- Planned lemma: joint_count_lower, keeping constants and the finite-depth error explicit. -/
def JointCountLower : Prop :=
  ∀ p : CounterProgram, ∀ C K : ℝ, 0 < C → 0 < K →
  (∀ (d m : ℕ) (s : State d) (η : ℝ) (P : Fin m → Measurement d) (u : Fin m → Mat d),
    0 < d → 0 ≤ η → TriangularRelations s η P u → C*m^4*η^2 ≤ 1/2 →
    Real.logb 2 d ≥ binaryCount P + activeSum s P - C*m^3*η -
      m*(binaryEntropy (C*m^4*η^2)+C*m^4*η^2)) →
  ∀ (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ)
    (r : JointFamily m M K), 0 ≤ δ →
    C*(4*M)^4*(jointError M δ K)^2 ≤ 1/2 →
    (3+expectation m.state (modelValue m 18))*M - 2*(M:ℝ)^2*δ -
      countPenalty C M (jointError M δ K) ≤ Real.logb 2 d

end
end E2.Turn9

