import E2.MomentProduct

namespace E2.ExactCompactness
noncomputable section
variable {A : Type*} [CStarAlgebra A]

def centralizer (φ : A →L[ℂ] ℂ) (hstar : ∀ x, φ (star x)=star (φ x)) : StarSubalgebra ℂ A where
  carrier := {x | ∀ y, φ (x*y)=φ (y*x)}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x z hx hz y
    simp only [add_mul,mul_add,map_add,hx y,hz y]
  mul_mem' := by
    intro x z hx hz y
    calc
      φ (x*z*y)=φ ((z*y)*x) := by rw [mul_assoc,hx]
      _=φ (z*(y*x)) := by rw [mul_assoc]
      _=φ ((y*x)*z) := hz _
      _=φ (y*(x*z)) := by rw [mul_assoc]
  algebraMap_mem' := by
    intro r y
    simp only [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  star_mem' := by
    intro x hx y
    have hh := congrArg star (hx (star y))
    simpa only [←hstar,star_mul,star_star] using hh.symm

instance centralizer_closed (φ : A →L[ℂ] ℂ) (hstar : ∀ x, φ (star x)=star (φ x)) :
    IsClosed (centralizer φ hstar : Set A) := by
  change IsClosed {x | ∀ y, φ (x*y)=φ (y*x)}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro y
  exact isClosed_eq (φ.continuous.comp (continuous_id.mul continuous_const))
    (φ.continuous.comp (continuous_const.mul continuous_id))

def centralizerState (φ : A →L[ℂ] ℂ) (hstar : ∀ x, φ (star x)=star (φ x))
    (hpos : ∀ x, 0≤(φ (star x*x)).re) (h1 : φ 1=1) : TracialState (centralizer φ hstar) where
  toLinearMap := φ.toLinearMap.comp (centralizer φ hstar).subtype.toLinearMap
  normalized := h1
  positive x := hpos x
  cyclic x y := x.property y

theorem closedSubalgebra_domain (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (d : Domain) (x : S) (hx : d.HoldsC (x:A)) : d.HoldsC x := by
  cases d with
  | positiveContraction =>
    apply positive_of_norms
    · change star x=x
      exact Subtype.ext hx.1
    · exact ExactForcing.contraction_norm (x:A) hx.1 hx.2
    · have hc := positive_complement (x:A) hx
      exact ExactForcing.contraction_norm ((1:A)-(x:A)) hc.1 hc.2
  | projection => exact ⟨Subtype.ext hx.1,Subtype.ext hx.2⟩
  | unitary => exact ⟨Subtype.ext hx.1,Subtype.ext hx.2⟩
  | reflection => exact ⟨Subtype.ext hx.1,Subtype.ext hx.2⟩

end
end E2.ExactCompactness
