import E2.CompilerNormalizedCorner

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial
variable {ι : Type*} [Fintype ι]

/-- Every original source relation is a finite consequence of the actual game. -/
theorem decoded_relation_certificate (P : Presentation ι) (r : Fin P.relations.length) :
    image (augmented (realize P)).relations (decodedRelation P r) = 0 := by
  apply CompilerMultiSelector.source_from_zero_corner
    (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true)
    (fun i => value (tables P) (Z P r i))
    (image (augmented (realize P)).relations (cornerPolynomial P r)) _
    (normalization P r) (ne_of_gt (normalization_pos P r))
  · exact zero_corner_certificate P r
  · have h := normalized_corner_certificate P r
    simp only [normalizedCornerResidual,image_sub,image_mul,selectorPolynomial,
      CompilerMultiSelector.image_ordered,CompilerMultiSelector.image_atom] at h
    exact sub_eq_zero.mp h
  · exact decoded_source_commute P r
  · have h := realized_twirl P r
    rw [selector_and] at h
    exact h

/-- The actual finite game yields a source model in precisely the supplied
local dimension and with precisely the supplied state. -/
theorem realize_soundness (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧ ∀ (η : ℝ) (d : ℕ)
      (m : Model (booleanPresentation (realize P)) d η), 0≤η →
      ∃ out : Model P d (C*η), out.state=m.state := by
  obtain ⟨C,hC,h⟩ := source_reconstruction_from_certificates P (augmented (realize P))
    (fun _ => rfl) (fun s => label P (source P s)) (by
      intro p hp
      obtain ⟨r,hr⟩ := List.mem_iff_get.mp hp
      subst p
      exact decoded_relation_certificate P r)
  refine ⟨C,hC,?_⟩
  intro η d m hη
  exact h η d (augmentModel (realize P) m hη) hη

end
end E2.CompilerNetwork
