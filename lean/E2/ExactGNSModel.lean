import E2.ExactTracialGNS
import E2.ExactPolyEval

namespace E2.ExactTrace
noncomputable section
open scoped ComplexOrder
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- Every frozen generator domain is preserved by a unital star homomorphism. -/
theorem domain_map (f : A →⋆ₐ[ℂ] B) (d : Domain) (a : A) (ha : d.HoldsC a) :
    d.HoldsC (f a) := by
  cases d with
  | positiveContraction =>
    refine ⟨ha.1.map f,?_⟩
    exact (AlgHom.spectrum_apply_subset (f.restrictScalars ℝ).toAlgHom a).trans ha.2
  | projection =>
    exact ⟨by rw [←map_star,ha.1],by rw [←map_mul,ha.2]⟩
  | reflection =>
    exact ⟨by rw [←map_star,ha.1],by rw [←map_mul,ha.2,map_one]⟩
  | unitary =>
    exact ⟨by rw [←map_star,←map_mul,ha.1,map_one],by rw [←map_star,←map_mul,ha.2,map_one]⟩

/-- Polynomial interpretation commutes with the exact model transport. -/
theorem eval_map {ι : Type*} (f : A →⋆ₐ[ℂ] B) (v : ι → A) (p : Poly ι) :
    p.evalC (fun i => f (v i))=f (p.evalC v) := by
  induction p with
  | const q => simp only [Poly.evalC,map_smul,map_one]
  | var i => rfl
  | add p q hp hq => simp only [Poly.evalC,hp,hq,map_add]
  | mul p q hp hq => simp only [Poly.evalC,hp,hq,map_mul]
  | adj p hp => simp only [Poly.evalC,hp,map_star]

/-- A faithful fully-positive tracial exact model preserving real self-adjoint
moments of the frozen weak functional. -/
def faithfulModel {ι : Type*} {P : Presentation ι} (m : ExactModel P A) :
    ExactModel P (FaithfulGNSAlgebra m.state) where
  state := quotientState m.state
  value i := quotientMap m.state (m.value i)
  domains i := domain_map (quotientMap m.state) (P.domain i) (m.value i) (m.domains i)
  equations r hr := by
    rw [eval_map,m.equations r hr,map_zero]

theorem faithfulModel_faithful {ι : Type*} {P : Presentation ι} (m : ExactModel P A)
    (z : FaithfulGNSAlgebra m.state) :
    (faithfulModel m).state.toLinearMap (star z*z)=0 → z=0 :=
  quotientState_faithful m.state z

theorem faithfulModel_preserves {ι : Type*} {P : Presentation ι} (m : ExactModel P A)
    (r : Poly ι) (hr : IsSelfAdjoint (r.evalC m.value)) :
    ((faithfulModel m).state.toLinearMap (r.evalC (faithfulModel m).value)).re=
      (m.state.toLinearMap (r.evalC m.value)).re := by
  change ((quotientState m.state).toLinearMap (r.evalC (fun i => quotientMap m.state (m.value i)))).re=_
  rw [eval_map,quotientState_preserves,hermitianPart_re m.state _ hr]

end
end E2.ExactTrace
