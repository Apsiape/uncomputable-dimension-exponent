import E2.CompilerUpperTableBounds

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks E2.CompilerStrategy E2.FiniteConstruction
variable {V : Type*} [Fintype V] [Nonempty V] {d : ℕ}

/-- Every original game incidence inherits the local table estimate. -/
theorem table_bounds_contexts (ts : List (Table V)) (x : V → Mat d)
    (hx : ∀ v, Domain.reflection.Holds (x v)) (state : State d) (ε : ℝ) (hε : 0≤ε)
    (hlocal : ∀ t ∈ ts, ∃ A : TableMeasurement t d,
      ∀ v ∈ t.scope, weighted state (A.marginal v-decodeProjection (x v))≤ε) :
    ∃ B : ContextPVM (game ts) d,
      ∀ c v, v ∈ (game ts).scope c →
        weighted state (B.marginal c v-decodeProjection (x ((Fintype.equivFin V).symm v)))≤ε := by
  classical
  have hh (i : Fin ts.length) := hlocal (ts.get i) (List.get_mem _ _)
  choose A hA using hh
  obtain ⟨B,hzero,hB⟩ := table_measurements_contexts ts x hx A
  refine ⟨B,?_⟩
  intro c
  refine Fin.cases ?_ (fun i => ?_) c
  · intro v hv
    change v ∈ ({0}:Finset (Fin (Fintype.card V))) at hv
    have he : v=(0:Fin (Fintype.card V)) := Finset.mem_singleton.mp hv
    subst v
    simpa [hzero] using hε
  · intro v hv
    change v ∈ (ts.get i).scope.image (Fintype.equivFin V) at hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [hB i w,Equiv.symm_apply_apply]
    exact hA i w hw

/-- Step 4: all concrete contexts and every incidence, with a uniform linear bound. -/
theorem flat_upper_contexts {ι : Type*} [Fintype ι] (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧
      ∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0≤δ → m.Flat →
      ∃ s : Model (E2.CompilerFrontend.reflectionPresentation P) (2*d) δ, s.Flat ∧
      ∃ aux : GadgetKey P → GadgetWire → Mat (wireDimension P d),
        (∀ w, Domain.reflection.Holds (wireValue P s.value aux w)) ∧
      ∃ A : ContextPVM (realize P) (wireDimension P d),
        ∀ (c : Fin (realize P).contexts) (v : Fin (realize P).numVars), v ∈ (realize P).scope c →
          weighted (flatState (wireDimension P d)
            (by have := registerSize_pos P; have := m.positive_dimension; unfold wireDimension; positivity))
            (A.marginal c v-decodeProjection
              (wireValue P s.value aux ((Fintype.equivFin (Wire P)).symm v))) ≤ C*δ := by
  obtain ⟨C,hC,h⟩ := flat_upper_repaired_wire_family P
  refine ⟨C,hC,?_⟩
  intro δ d m hδ hm
  obtain ⟨s,hs,aux,R,hdom,hgen,hsix,hR,hd,hfactor⟩ := h δ d m hδ hm
  refine ⟨s,hs,aux,hdom,?_⟩
  apply table_bounds_contexts (tables P) (wireValue P s.value aux) hdom _ (C*δ) (mul_nonneg hC.le hδ)
  intro t ht
  obtain ⟨r,_,ht⟩ := List.mem_flatMap.mp ht
  exact actual_relation_table_bounds P s.value aux hdom hgen hsix _ (C*δ) (mul_nonneg hC.le hδ)
    R (fun r => ⟨(hR r).1,(hR r).2.1,(hR r).2.2.1,(hR r).2.2.2.1⟩) r t ht

/-- Step 5: flat quadratic-loss completeness for the actual unchanged game. -/
theorem realize_completeness {ι : Type*} [Fintype ι] (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧ ∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0≤δ → m.Flat →
      ∃ d', 0<d' ∧ d'≤wireDimensionFactor P*d ∧
        ∃ S : Strategy (realize P) d', loss S≤C*δ^2 := by
  obtain ⟨C,hC,h⟩ := flat_upper_contexts P
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro δ d m hδ hm
  obtain ⟨s,hs,aux,hdom,A,hA⟩ := h δ d m hδ hm
  have hd : 0<wireDimension P d := by
    have := registerSize_pos P
    have := m.positive_dimension
    unfold wireDimension
    positivity
  let Q := fun v => decodeProjection (wireValue P s.value aux ((Fintype.equivFin (Wire P)).symm v))
  have hQ (v) : Domain.projection.Holds (Q v) := decode_projection _ (hdom _)
  refine ⟨wireDimension P d,hd,?_,A.strategy hd Q hQ,?_⟩
  · exact (wireDimension_eq P d).le
  · exact A.quadratic_loss hd Q hQ δ C hδ hC.le hA

end
end E2.CompilerUpper

