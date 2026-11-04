import E2.CompilerReflectionLift

namespace E2.CompilerFrontend
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open E2.CompilerDomains E2.CompilerRealification E2.FiniteConstruction
open Companion.Analytic
variable {ι : Type*} {d : ℕ}

/-- Every source domain has two reflection coordinates on the same space. -/
theorem lift_source_coordinates (P : Presentation ι) (x : ι → Mat d)
    (hx : ∀ i, (P.domain i).Holds (x i)) :
    ∃ y : ι × Fin 2 → Mat (2*d),
      (∀ j, Domain.reflection.Holds (y j)) ∧
      ∀ i, Poly.eval y (replacement P i) = realify (x i) := by
  classical
  have localLift (i : ι) : ∃ y : Fin 2 → Mat (2*d),
      (∀ j, Domain.reflection.Holds (y j)) ∧
      (match P.domain i with
      | .reflection => y 0
      | .projection => decodeProjection (y 0)
      | .unitary => y 0*y 1
      | .positiveContraction => decodePositive (y 0*y 1)) = realify (x i) := by
    have hi := hx i
    cases hd : P.domain i with
    | reflection =>
      have hr := realify_domain _ _ (show Domain.reflection.Holds (x i) from hd ▸ hi)
      refine ⟨![realify (x i),1],?_,?_⟩
      · intro j; fin_cases j
        · exact hr
        · exact ⟨by simp,by simp⟩
      · simp
    | projection =>
      have hp := realify_domain _ _ (show Domain.projection.Holds (x i) from hd ▸ hi)
      refine ⟨![encodeProjection (realify (x i)),1],?_,?_⟩
      · intro j; fin_cases j
        · exact encode_projection _ hp
        · exact ⟨by simp,by simp⟩
      · simp
    | unitary =>
      obtain ⟨A,B,hA,hB,he⟩ := realified_unitary_factors (x i) (hd ▸ hi)
      refine ⟨![A,B],?_,?_⟩
      · intro j; fin_cases j <;> assumption
      · simpa using he
    | positiveContraction =>
      obtain ⟨U,hU,hdec⟩ := positive_unitary_lift (x i) (hd ▸ hi)
      obtain ⟨A,B,hA,hB,he⟩ := realified_unitary_factors U hU
      refine ⟨![A,B],?_,?_⟩
      · intro j; fin_cases j <;> assumption
      · change decodePositive (A*B) = realify (x i)
        rw [he]
        calc
          decodePositive (realify U) = realify (decodePositive U) := by
            have hc : (1/4 : ℂ) = ((1/4 : ℚ) : ℂ) := by norm_num
            simp only [decodePositive,hc,realify_rat_smul,realify_add,realify_one,
              ← Matrix.star_eq_conjTranspose,realify_star]
          _ = realify (x i) := congrArg realify hdec
  choose y hy hdec using localLift
  refine ⟨fun j => y j.1 j.2,fun j => hy j.1 j.2,?_⟩
  intro i
  have he := hdec i
  cases hd : P.domain i <;>
    simpa [replacement,unitaryWord,Poly.eval,hd,decodeProjection,decodePositive] using he

/-- The decoder agrees with one homomorphic embedding on every polynomial,
including products of generators in different source domains and adjoints. -/
theorem eval_lifted_source (P : Presentation ι) (x : ι → Mat d)
    (y : ι × Fin 2 → Mat (2*d))
    (hy : ∀ i, Poly.eval y (replacement P i) = realify (x i)) (p : Poly ι) :
    Poly.eval y (substitute (replacement P) p) = realify (Poly.eval x p) := by
  rw [eval_substitute]
  simpa only [hy] using eval_realify x p

/-- The complete simultaneous flat reflection extension has factor two in
dimension and no increase in error. Its state commutators vanish exactly. -/
theorem flat_reflection_extension (P : Presentation ι) (δ : ℝ)
    (m : Model P d δ) (hδ : 0≤δ) (hm : m.Flat) :
    ∃ out : Model (reflectionPresentation P) (2*d) δ,
      out.Flat ∧
      (∀ p : Poly ι, Poly.eval out.value (substitute (replacement P) p) =
        realify (Poly.eval m.value p)) ∧
      (∀ p : Poly ι, weighted out.state (Poly.eval out.value (substitute (replacement P) p)) =
        weighted m.state (Poly.eval m.value p)) ∧
      (∀ j, ‖out.value j‖ ≤ 1) ∧
      (∀ j, comm (out.value j) out.state.xi = 0) := by
  obtain ⟨y,hy,hdec⟩ := lift_source_coordinates P m.value m.domains
  have hd : 0<2*d := by have := m.positive_dimension; omega
  have he (p : Poly ι) := eval_lifted_source P m.value y hdec p
  let out : Model (reflectionPresentation P) (2*d) δ := {
    positive_dimension := hd
    state := flatState (2*d) hd
    value := y
    domains := hy
    defects := by
      intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      rw [he,weighted_realify m.positive_dimension,
        ← CompilerFlat.flat_model_state m hm]
      exact m.defects p hp
    state_commutators := by
      intro j
      simpa [flatState_commutes,hs,hsNorm,hsSquared] using hδ }
  refine ⟨out,?_,he,?_,?_,?_⟩
  · simp [Model.Flat,out,flatState,one_div]
  · intro p
    change weighted (flatState (2*d) hd) (Poly.eval y _) = _
    rw [he,weighted_realify m.positive_dimension,← CompilerFlat.flat_model_state m hm]
  · intro j
    exact reflection_norm hd _ (hy j)
  · intro j
    exact flatState_commutes hd _

end
end E2.CompilerFrontend
