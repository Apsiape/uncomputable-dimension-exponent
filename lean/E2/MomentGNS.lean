import E2.MomentUltralimit

namespace E2.ExactCompactness
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem quotientMap_zero_of_square (τ : TracialState A) (x : A)
    (hx : τ.toLinearMap (star x*x)=0) : ExactTrace.quotientMap τ x=0 := by
  apply ExactTrace.quotientState_faithful τ
  rw [←map_star,←map_mul,ExactTrace.quotientState_preserves]
  have hs : star (star x*x)=star x*x := by simp only [star_mul,star_star]
  change (1/2:ℂ)*(τ.toLinearMap (star x*x)+star (τ.toLinearMap (star (star x*x))))=0
  rw [hs,hx]
  simp

def exactModelOfMoments {ι : Type*} (P : Presentation ι) (τ : TracialState A) (x : ι → A)
    (hd : ∀ i, (P.domain i).HoldsC (x i))
    (hr : ∀ r ∈ P.relations, τ.toLinearMap (star (r.evalC x)*r.evalC x)=0) :
    ExactModel P (ExactTrace.FaithfulGNSAlgebra τ) where
  state := ExactTrace.quotientState τ
  value i := ExactTrace.quotientMap τ (x i)
  domains i := ExactTrace.domain_map _ _ _ (hd i)
  equations r h := by
    rw [ExactTrace.eval_map]
    exact quotientMap_zero_of_square τ _ (hr r h)

theorem exactModelOfMoments_preserves {ι : Type*} (P : Presentation ι) (τ : TracialState A) (x : ι → A)
    (hd : ∀ i, (P.domain i).HoldsC (x i))
    (hr : ∀ r ∈ P.relations, τ.toLinearMap (star (r.evalC x)*r.evalC x)=0)
    (r : Poly ι) (hsa : IsSelfAdjoint (r.evalC x)) :
    ((exactModelOfMoments P τ x hd hr).state.toLinearMap
      (r.evalC (exactModelOfMoments P τ x hd hr).value)).re=(τ.toLinearMap (r.evalC x)).re := by
  change ((ExactTrace.quotientState τ).toLinearMap (r.evalC (fun i => ExactTrace.quotientMap τ (x i)))).re=_
  rw [ExactTrace.eval_map,ExactTrace.quotientState_preserves,ExactTrace.hermitianPart_re τ _ hsa]

end
end E2.ExactCompactness
