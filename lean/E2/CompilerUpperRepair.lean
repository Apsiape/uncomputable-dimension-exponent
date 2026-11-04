import E2.CompilerUpperOverlap

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks E2.FiniteConstruction Companion.Analytic
variable {ι : Type*} [Fintype ι] {d : ℕ}

@[simp] theorem decode_duplicate (M : Mat d) :
    decodeProjection (duplicate M)=duplicate (decodeProjection M) := by
  simp only [decodeProjection,duplicate_smul,duplicate_add,duplicate_one]

/-- The last actual conjugacy wire, including the zero-step branch. -/
theorem wireValue_F (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (r : Fin P.relations.length) :
    wireValue P s aux (F P r)=duplicate (duplicate (baseConjugate P s r (steps P r))) := by
  unfold F
  split_ifs with h
  · rw [wireValue_E]
    simp only [h,baseConjugate,List.take_zero,conjugateList,List.foldl_nil]
  · rw [wireValue_conjugate]
    congr 2
    congr 1
    dsimp
    omega

/-- Both ancillary doublings preserve the overlap flat norm exactly. -/
theorem wire_overlap_transport (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hd : 0<d) (aux) (r : Fin P.relations.length) :
    weighted (flatState (2*(2*(registerSize P*d))) (by have := registerSize_pos P; positivity))
      (decodeProjection (wireValue P s aux (E P r))*decodeProjection (wireValue P s aux (F P r))) =
    weighted (flatState (registerSize P*d) (Nat.mul_pos (registerSize_pos P) hd))
      (decodeProjection (baseE P r)*decodeProjection (baseConjugate P s r (steps P r))) := by
  rw [wireValue_E,wireValue_F]
  simp only [decode_duplicate,← duplicate_mul]
  rw [weighted_duplicate (by have := registerSize_pos P; positivity),
    weighted_duplicate (Nat.mul_pos (registerSize_pos P) hd)]

/-- Simultaneous same-space repair of every actual F projection, with one
constant for the whole presentation. All other wire matrices are already fixed. -/
theorem flat_wire_orthogonality_repair (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧ ∀ (δ : ℝ) (d : ℕ)
      (s : Model (E2.CompilerFrontend.reflectionPresentation P) d δ), 0≤δ → s.Flat →
      ∀ aux : GadgetKey P → GadgetWire → Mat (2*(2*(registerSize P*d))),
      ∃ R : Fin P.relations.length → Mat (2*(2*(registerSize P*d))),
      ∀ r : Fin P.relations.length,
        Domain.projection.Holds (R r) ∧
        decodeProjection (wireValue P s.value aux (E P r))*R r=0 ∧
        R r*decodeProjection (wireValue P s.value aux (E P r))=0 ∧
        weighted (flatState (2*(2*(registerSize P*d)))
          (by have := registerSize_pos P; have := s.positive_dimension; positivity))
          (R r-decodeProjection (wireValue P s.value aux (F P r)))≤C*δ ∧
        weighted (flatState (2*(2*(registerSize P*d)))
          (by have := registerSize_pos P; have := s.positive_dimension; positivity))
          (R r-decodeProjection (wireValue P s.value aux (F P r)))^2≤C^2*δ^2 := by
  obtain ⟨C,hC,hbound⟩ := flat_base_overlap P
  refine ⟨6*C,by positivity,?_⟩
  intro δ d s hδ hs aux
  have hd : 0<2*(2*(registerSize P*d)) := by
    have := registerSize_pos P
    have := s.positive_dimension
    positivity
  have hE (r) : Domain.projection.Holds (decodeProjection (wireValue P s.value aux (E P r))) := by
    rw [wireValue_E,decode_duplicate,decode_duplicate]
    exact duplicate_domain _ _ (duplicate_domain _ _ (decode_projection _ (baseE_domain P r)))
  have hF (r) : Domain.projection.Holds (decodeProjection (wireValue P s.value aux (F P r))) := by
    rw [wireValue_F,decode_duplicate,decode_duplicate]
    exact duplicate_domain _ _ (duplicate_domain _ _
      (decode_projection _ (baseConjugate_domain P s.value s.domains r _)))
  have hrepair (r : Fin P.relations.length) :=
    E2.CompilerOrthogonality.flat_orthogonality_repair hd
      (decodeProjection (wireValue P s.value aux (E P r)))
      (decodeProjection (wireValue P s.value aux (F P r))) (hE r) (hF r)
      (C*δ) (mul_nonneg hC.le hδ) (by
        rw [wire_overlap_transport P s.value s.positive_dimension]
        exact hbound δ d s hδ hs r)
  choose R hdom hER hRE hclose hsq using hrepair
  refine ⟨R,fun r => ⟨hdom r,hER r,hRE r,?_,?_⟩⟩
  · simpa only [mul_assoc] using hclose r
  · convert hsq r using 1 <;> ring


/-- Steps 1--3 assembled for the original source model on the common wire space. -/
theorem flat_upper_repaired_wire_family (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧ ∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0≤δ → m.Flat →
    ∃ s : Model (E2.CompilerFrontend.reflectionPresentation P) (2*d) δ, s.Flat ∧
    ∃ aux : GadgetKey P → GadgetWire → Mat (wireDimension P d),
    ∃ R : Fin P.relations.length → Mat (wireDimension P d),
      (∀ w, Domain.reflection.Holds (wireValue P s.value aux w)) ∧
      (∀ k, GeneralData (fun i => wireValue P s.value aux (gadgetInputs P k i))
        (fun j => aux k (.inl j))) ∧
      (∀ k i, SixData (subA (fun j => aux k (.inl j)) i)
        (subB (fun j => aux k (.inl j)) i) (subC (fun j => aux k (.inl j)) i)
        (fun j => aux k (.inr (i,j)))) ∧
      (∀ r, Domain.projection.Holds (R r) ∧
        decodeProjection (wireValue P s.value aux (E P r))*R r=0 ∧
        R r*decodeProjection (wireValue P s.value aux (E P r))=0 ∧
        weighted (flatState (wireDimension P d)
          (by have := registerSize_pos P; have := m.positive_dimension; unfold wireDimension; positivity))
          (R r-decodeProjection (wireValue P s.value aux (F P r)))≤C*δ ∧
        weighted (flatState (wireDimension P d)
          (by have := registerSize_pos P; have := m.positive_dimension; unfold wireDimension; positivity))
          (R r-decodeProjection (wireValue P s.value aux (F P r)))^2≤C^2*δ^2) ∧
      0<wireDimension P d ∧ wireDimension P d ≤ wireDimensionFactor P*d := by
  obtain ⟨C,hC,hrepair⟩ := flat_wire_orthogonality_repair P
  refine ⟨C,hC,?_⟩
  intro δ d m hδ hm
  obtain ⟨s,hs,aux,hdom,hgen,hsix,_,_,_,hd,hfactor⟩ := flat_upper_wire_family P δ d m hδ hm
  obtain ⟨R,hR⟩ := hrepair δ (2*d) s hδ hs aux
  exact ⟨s,hs,aux,R,hdom,hgen,hsix,hR,hd,hfactor⟩

end
end E2.CompilerUpper
