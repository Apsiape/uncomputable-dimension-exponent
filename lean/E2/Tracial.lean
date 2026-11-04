import E2.ExactClockTheorem
import E2.ExactIncrementModel
import E2.ExactSourceDefs
import E2.ExactResetModel
import E2.ExactFlagDensity
import E2.UniformFlagDensity

namespace E2
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

/-- Proposition 4.5, exact guarded increment. Faithfulness is stated explicitly;
the general exact flag argument passes to the faithful tracial GNS quotient. -/
theorem exact_increment (m : ExactModel clockPresentation A) (v : A)
    (hv : Domain.unitary.HoldsC v)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (guard : (v - m.value 3 * ((1-m.value 1) +
      (m.value 2*v*star (m.value 2))*m.value 1))*(1-m.value 0)=0) :
    ∀ M bits, star v * cylinder (fun j => ctranslate (m.value 2) (m.value 1) j) M bits * v =
      cylinder (fun j => ctranslate (m.value 2) (m.value 1) j) M
        (fun j => decide ((((∑ k : Fin M, if bits k then 2^k.val else 0) + 2^M - 1) / 2^j.val) % 2 = 1)) := by
  exact ExactClock.model_increment m v hv faithful guard

/-- Lemma 6.1, finite decoding and reset identities. -/
theorem forced_initialization (p : CounterProgram) (m : ExactModel (sourcePresentation p) A) :
    (∀ e, addressCylinder m e * sourceValue m 15 = addressCylinder m e) ∧
    (∀ e, addressCylinder m e * sourceValue m 16 = ((2:ℂ)^(-(e:ℤ))) • addressCylinder m e) ∧
    (∀ k, fuelCylinder m k * sourceValue m 17 = fuelCylinder m k * timeZeroCylinder m k) := by
  exact ⟨(ExactForcing.address_initialization m).1,
    (ExactForcing.address_initialization m).2,ExactForcing.reset_initialization m⟩

/-- Zero-test clause of Lemma 6.1, as a right-action statement on a projection. -/
theorem forced_zero_test (r z s q : A)
    (hr : Domain.positiveContraction.HoldsC r) (hz : Domain.projection.HoldsC z)
    (hs : Domain.positiveContraction.HoldsC s) (hq : Domain.projection.HoldsC q)
    (hcomm : z*s=s*z) (heq : r=z+(1/2:ℂ) • ((1-z)*s))
    (n : ℕ) (hencoded : r*q=((2:ℂ)^(-(n:ℤ))) • q) :
    z*q = if n=0 then q else 0 := by
  exact ExactForcing.zero_test r z s q hz.2 hcomm
    (ExactForcing.contraction_norm s hs.1 hs.2) heq n hencoded

/-- Exact part of Theorem 6.2, retaining the recognizer correctness premise. -/
theorem exact_flag_density (p : CounterProgram) (hp : RecognizesK p)
    (m : ExactModel (sourcePresentation p) A) :
    thetaK ≤ (m.state.toLinearMap (sourceValue m 18)).re := by
  exact ExactForcing.model_flag_density p hp m

/-- Uniform weighted part of Theorem 6.2, stated without an effective modulus. -/
theorem uniform_flag_density (p : CounterProgram) (hp : RecognizesK p) :
    ∃ ω : ℝ → ℝ, Filter.Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (δ : ℝ) (d : ℕ) (m : Model (sourcePresentation p) d δ), 0 < δ →
        thetaK - ω δ ≤ expectation m.state (Poly.eval m.value (sv p 18)) := by
  exact ExactCompactness.model_uniform_flag_density p hp

end
end E2


