import E2.CompilerUpperWires

namespace E2.CompilerUpper
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerBlocks E2.CompilerFrontend E2.CompilerRealification
open E2.FiniteConstruction Companion.Analytic
variable {ι : Type*}

def wireDimensionFactor (P : Presentation ι) : ℕ := 8*registerSize P
abbrev wireDimension (P : Presentation ι) (d : ℕ) : ℕ := 2*(2*(registerSize P*(2*d)))

theorem wireDimensionFactor_pos (P : Presentation ι) : 0<wireDimensionFactor P := by
  have := registerSize_pos P
  unfold wireDimensionFactor
  positivity

theorem wireDimension_eq (P : Presentation ι) (d : ℕ) : wireDimension P d=wireDimensionFactor P*d := by
  unfold wireDimension wireDimensionFactor
  ring

/-- Steps 1 and 2 of upper realization on the actual wire set: exact source
transport, all common-space reflections, and every Boolean conjugacy gadget.
This does not assert legality of the final orthogonality contexts. -/
theorem flat_upper_wire_family (P : Presentation ι) (δ : ℝ) (d : ℕ)
    (m : Model P d δ) (hδ : 0≤δ) (hm : m.Flat) :
    ∃ s : Model (reflectionPresentation P) (2*d) δ, s.Flat ∧
      ∃ aux : GadgetKey P → GadgetWire → Mat (wireDimension P d),
      (∀ w, Domain.reflection.Holds (wireValue P s.value aux w)) ∧
      (∀ k, GeneralData (fun i => wireValue P s.value aux (gadgetInputs P k i))
        (fun j => aux k (.inl j))) ∧
      (∀ k i, SixData (subA (fun j => aux k (.inl j)) i)
        (subB (fun j => aux k (.inl j)) i) (subC (fun j => aux k (.inl j)) i)
        (fun j => aux k (.inr (i,j)))) ∧
      (∀ p : Poly ι, weighted
        (flatState (wireDimension P d) (by have := registerSize_pos P; have := m.positive_dimension; positivity))
        (Poly.eval (fun j => wireValue P s.value aux (E2.CompilerNetwork.source P j))
          (substitute (replacement P) p)) = weighted m.state (Poly.eval m.value p)) ∧
      (∀ w, ‖wireValue P s.value aux w‖ ≤ 1) ∧
      (∀ w, comm (wireValue P s.value aux w)
        (flatState (wireDimension P d) (by have := registerSize_pos P; have := m.positive_dimension; positivity)).xi=0) ∧
      0<wireDimension P d ∧ wireDimension P d ≤ wireDimensionFactor P*d := by
  obtain ⟨s,hs,_,hweighted,_,_⟩ := flat_reflection_extension P δ m hδ hm
  obtain ⟨aux,hdom,hgen,hsix,hnorm,hstate⟩ := upper_wire_extension P s.value s.positive_dimension s.domains
  refine ⟨s,hs,aux,hdom,?_,hsix,?_,hnorm,hstate,?_,?_⟩
  · intro k
    simpa only [wireValue_gadgetInputs] using hgen k
  · intro p
    rw [wireValue_source_weighted P s.value s.positive_dimension]
    rw [← CompilerFlat.flat_model_state s hs]
    exact hweighted p
  · have := registerSize_pos P
    have := m.positive_dimension
    unfold wireDimension
    positivity
  · exact (wireDimension_eq P d).le

end
end E2.CompilerUpper
