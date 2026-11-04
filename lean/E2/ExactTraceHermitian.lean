import E2.ExactTraceReal

namespace E2.ExactTrace
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- Canonical Hermitian trace; no change to the frozen state definition. -/
def hermitianPart (τ : TracialState A) : TracialState A where
  toLinearMap := {
    toFun := fun a => (1/2:ℂ)*(τ.toLinearMap a+star (τ.toLinearMap (star a)))
    map_add' := by
      intro a b
      simp only [map_add,star_add]
      ring
    map_smul' := by
      intro c a
      simp only [star_smul,map_smul,smul_eq_mul,star_mul,star_star,RingHom.id_apply]
      ring }
  normalized := by
    change (1/2:ℂ)*(τ.toLinearMap 1+star (τ.toLinearMap (star (1:A))))=1
    rw [star_one,τ.normalized]
    norm_num
  positive a := by
    have hs : star (star a*a)=star a*a := by simp only [star_mul,star_star]
    change 0≤((1/2:ℂ)*(τ.toLinearMap (star a*a)+star (τ.toLinearMap (star (star a*a))))).re
    rw [hs]
    simpa [Complex.star_def,Complex.mul_re] using τ.positive a
  cyclic a b := by
    change (1/2:ℂ)*(τ.toLinearMap (a*b)+star (τ.toLinearMap (star (a*b))))=
      (1/2:ℂ)*(τ.toLinearMap (b*a)+star (τ.toLinearMap (star (b*a))))
    rw [τ.cyclic a b]
    simp only [star_mul]
    rw [τ.cyclic (star b) (star a)]

 theorem hermitianPart_star (τ : TracialState A) (a : A) :
    (hermitianPart τ).toLinearMap (star a)=star ((hermitianPart τ).toLinearMap a) := by
  change (1/2:ℂ)*(τ.toLinearMap (star a)+star (τ.toLinearMap (star (star a))))=
    star ((1/2:ℂ)*(τ.toLinearMap a+star (τ.toLinearMap (star a))))
  simp only [star_mul,star_add,star_star]
  norm_num
  ring

 theorem hermitianPart_im (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    ((hermitianPart τ).toLinearMap a).im=0 := by
  have h := hermitianPart_star τ a
  rw [ha.star_eq] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith

 theorem hermitianPart_re (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) :
    ((hermitianPart τ).toLinearMap a).re=(τ.toLinearMap a).re := by
  change ((1/2:ℂ)*(τ.toLinearMap a+star (τ.toLinearMap (star a)))).re=_
  rw [ha.star_eq]
  simp [Complex.star_def,Complex.mul_re]
  ring

open scoped ComplexOrder in
 theorem hermitianPart_square_nonneg (τ : TracialState A) (z : A) :
    0≤(hermitianPart τ).toLinearMap (star z*z) := by
  exact Complex.nonneg_iff.mpr ⟨(hermitianPart τ).positive z,
    (hermitianPart_im τ (star z*z) (IsSelfAdjoint.star_mul_self z)).symm⟩
 theorem top_projection_hermitian (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (hσ : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hmom : Filter.Tendsto (fun n : ℕ => (τ.toLinearMap (a^n)).re) Filter.atTop (nhds 0))
    (e : A) (he : star e=e) (hee : e*e=e) (hae : a*e=e)
    (him : (τ.toLinearMap e).im=0) : τ.toLinearMap e=0 := by
  apply Complex.ext
  · exact top_projection_real τ a ha hσ hmom e he hee hae
  · exact him

end
end E2.ExactTrace




