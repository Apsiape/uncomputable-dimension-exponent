import E2.AffineDigits

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- Full construction from the affine hypotheses of Remark 4.3. This is a
proved theorem, with an explicit absolute constant, rather than a literature input. -/
theorem affine_spectral_repair_construction : ∃ C : ℝ, 0<C ∧ ∀ (d : ℕ) (s : State d)
    (δ : ℝ) (c : ClockData d), 0≤δ → Domain.positiveContraction.Holds c.A →
    Domain.projection.Holds c.P → Domain.unitary.Holds c.T →
    weighted s (comm c.A c.P)≤δ →
    weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))≤δ →
    hs (comm c.A s.xi)≤δ → hs (comm c.P s.xi)≤δ → hs (comm c.T s.xi)≤δ →
    Nonempty (SpectralRepair c s δ C) := by
  refine ⟨20000,by norm_num,?_⟩
  intro d s δ c hδ hA hP hT hAP hAff hσA hσP hσT
  obtain ⟨Ahat,hK,hclose,hσ,hbase⟩ := affine_cantor_rounding s δ c hδ hA hP hT hAP hAff hσA hσP hσT
  have htail := repaired_affine_tail s δ c Ahat hδ hA hT hK hσT hAff hclose hbase
  have hstep := spectral_digit_conjugation_error s δ Ahat c.T hδ hK hT hσ htail
  have hdigits := raw_digit_from_repair s δ c Ahat hδ hK hP hT hσT hbase hstep
  refine ⟨{Ahat := Ahat, spectrum := hK, closeness := ?_, digits := ?_}⟩
  · nlinarith only [hclose,hσ,hδ]
  · intro j
    have hp : 0≤(4:ℝ)^j*δ := mul_nonneg (pow_nonneg (by norm_num) j) hδ
    nlinarith only [hdigits j,hp]

end
end E2

#print axioms E2.affine_spectral_repair_construction
