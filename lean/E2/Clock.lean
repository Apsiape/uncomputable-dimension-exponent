import E2.FunctionalCalculus
import E2.AffineRepair
import E2.RawClockRepair
import E2.FiniteClockModel

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Lemma 4.2 (spectral and raw-digit clauses). -/
theorem clock_spectral_repair : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d)
    (δ : ℝ) (c : ClockData d), 0 ≤ δ → ClockApprox s δ c →
    Nonempty (SpectralRepair c s δ C) := by
  obtain ⟨C,hC,hrepair⟩ := affine_spectral_repair_construction
  refine ⟨C,hC,?_⟩
  intro d s δ c hδ hc
  apply hrepair d s δ c hδ hc.1.1 hc.1.2.1 hc.1.2.2.1
  · exact hc.2.1 _ (by simp [ClockData.defects])
  · exact hc.2.1 _ (by simp [ClockData.defects])
  · exact hc.2.2 _ (by simp [ClockData.variables])
  · exact hc.2.2 _ (by simp [ClockData.variables])
  · exact hc.2.2 _ (by simp [ClockData.variables])

def clockDigitError (M : ℕ) (δ C : ℝ) := C * (M+1)^3 * 4^M * δ

/-- The remaining raw-projection and triangular-flip conclusions of Lemma 4.2. -/
theorem clock_raw_digits : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d)
    (δ : ℝ) (c : ClockData d) (M : ℕ), 0 ≤ δ → ClockApprox s δ c →
    (∀ j < M, Domain.projection.Holds (rawDigit c j)) ∧
    (∀ j < M, Domain.reflection.Holds (rawFlip c j)) ∧
    (∀ j < M, ∀ k < M, weighted s (comm (rawDigit c j) (rawDigit c k)) ≤ clockDigitError M δ C) ∧
    (∀ j < M, weighted s (rawFlip c j * rawDigit c j * rawFlip c j - (1-rawDigit c j)) ≤ clockDigitError M δ C) ∧
    (∀ j < M, ∀ k < M, j < k → weighted s (comm (rawFlip c j) (rawDigit c k)) ≤ clockDigitError M δ C) ∧
    (∀ j < M, hs (comm (rawDigit c j) s.xi) ≤ clockDigitError M δ C) ∧
    (∀ j < M, hs (comm (rawFlip c j) s.xi) ≤ clockDigitError M δ C) := by
  obtain ⟨C₀,hC₀,hrepair⟩ := clock_spectral_repair
  let K := C₀+1
  have hK : 1≤K := by dsimp [K]; linarith
  refine ⟨100*K,by positivity,?_⟩
  intro d s δ c M hδ hc
  obtain ⟨r₀⟩ := hrepair d s δ c hδ hc
  let r : SpectralRepair c s δ K := {
    Ahat := r₀.Ahat
    spectrum := r₀.spectrum
    closeness := r₀.closeness.trans (by dsimp [K]; nlinarith)
    digits := fun j => (r₀.digits j).trans (by gcongr; dsimp [K]; linarith) }
  simpa only [clockDigitError,rawClockScale,mul_assoc] using raw_clock_estimates s δ K c hδ hK hc r M

def clockPresentation : Presentation (Fin 4) :=
  ⟨fun i => match i.val with
      | 0 => .positiveContraction | 1 => .projection | 2 => .unitary | _ => .reflection,
   clockRelations (.var 0) (.var 1) (.var 2) (.var 3)⟩

/-- Finite-model assertion in Theorem 4.4, independent of its lower bound. -/
theorem finite_clock (N : ℕ) (hN : 0 < N) :
    ∃ m : Model clockPresentation (2^N) (3 * (4:ℝ)^(-(N:ℤ))), m.Flat := by
  cases N with
  | zero => omega
  | succ n => exact ⟨FiniteConstruction.clockModel n,FiniteConstruction.clockModel_flat n⟩

/-- Finite-model part of Proposition 4.5, including both displayed norms. -/
theorem finite_increment (N : ℕ) (hN : 0 < N) :
    ∃ m : Model clockPresentation (2^N) (3*(4:ℝ)^(-(N:ℤ))), m.Flat ∧
      ∃ V : Mat (2^N), Domain.unitary.Holds V ∧
        let A := m.value 0
        let P := m.value 1
        let T := m.value 2
        let X := m.value 3
        let defect := (V-X*((1-P)+(T*V*T.conjTranspose)*P))*(1-A)
        ‖defect‖ = Real.sqrt 2*(4:ℝ)^(-(N:ℤ)) ∧
        weighted m.state defect = Real.sqrt 2*(4:ℝ)^(-(N:ℤ))/Real.sqrt ((2:ℝ)^N) := by
  sorry

/-- Proposition 4.6, including the weighted guard-removal estimate. -/
theorem guard_mass : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d) (c : ClockData d)
    (δ : ℝ) (M : ℕ), 0 ≤ δ → 1 ≤ M → ClockApprox s δ c →
    expectation s (matrixFunction (fun x => if 1-(4:ℝ)^(-(M:ℤ)) ≤ x ∧ x ≤ 1 then 1 else 0) c.A) ≤
      (2:ℝ)^(-(M:ℤ)) + C*(M+1)^5*4^M*δ := by
  sorry

theorem guard_remove : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d) (c : ClockData d)
    (δ L : ℝ) (M : ℕ) (R : Mat d), 0 ≤ δ → 1 ≤ M → ClockApprox s δ c →
    ‖R‖ ≤ L → weighted s (R*(1-c.A)) ≤ δ →
    weighted s R ≤ 4^M*(1+L)*δ + L*Real.sqrt ((2:ℝ)^(-(M:ℤ))+C*(M+1)^5*4^M*δ) := by
  sorry

end
end E2

#print axioms E2.clock_spectral_repair
#print axioms E2.clock_raw_digits
