import E2.Tracial
import E2.ExactClockNoTop

namespace E2
noncomputable section

/-- The hypotheses actually used by spectral repair, omitting every flip. -/
def AffineClockApprox {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d) : Prop :=
  Domain.positiveContraction.Holds c.A ∧ Domain.projection.Holds c.P ∧
  Domain.unitary.Holds c.T ∧ weighted s (comm c.A c.P) ≤ δ ∧
  weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P)) ≤ δ ∧
  hs (comm c.A s.xi) ≤ δ ∧ hs (comm c.P s.xi) ≤ δ ∧ hs (comm c.T s.xi) ≤ δ

/-- Remark 4.3, made explicit for use with the two conditional coordinates. -/
theorem affine_spectral_repair : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (s : State d)
    (δ : ℝ) (c : ClockData d), 0 ≤ δ → AffineClockApprox s δ c →
    Nonempty (SpectralRepair c s δ C) := by
  obtain ⟨C,hC,hrepair⟩ := affine_spectral_repair_construction
  refine ⟨C,hC,?_⟩
  intro d s δ c hδ ha
  rcases ha with ⟨hA,hP,hT,hAP,hAff,hσA,hσP,hσT⟩
  exact hrepair d s δ c hδ hA hP hT hAP hAff hσA hσP hσT

/-- Spectral no-atom clause of Lemma 4.1. The moment limit is an equivalent
spectral-measure formulation for a positive contraction; the projection clause
applies in the tracial von Neumann closure as well as in the original algebra. -/
theorem exact_clock_no_top_atom {A : Type*} [CStarAlgebra A]
    (m : ExactModel clockPresentation A) :
    Filter.Tendsto (fun n : ℕ => (m.state.toLinearMap ((m.value 0)^n)).re)
      Filter.atTop (nhds 0) ∧
    ∀ e : A, star e=e → e*e=e → m.value 0*e=e → m.state.toLinearMap e=0 := by
  exact ⟨ExactClock.model_moments_zero m,ExactClock.model_top_projection m⟩

theorem faithful_clock_no_top_projection {A : Type*} [CStarAlgebra A]
    (m : ExactModel clockPresentation A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (e : A) (he : star e=e) (hee : e*e=e) (hae : m.value 0*e=e) : e=0 := by
  apply faithful e
  rw [he,hee]
  exact (exact_clock_no_top_atom m).2 e he hee hae

end
end E2

#print axioms E2.affine_spectral_repair
