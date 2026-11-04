import E2.ExactTraceHermitian
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace E2.ExactTrace
noncomputable section
open scoped ComplexOrder InnerProductSpace Topology
variable {A : Type*} [CStarAlgebra A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The positive functional used for GNS is the Hermitian part of the frozen
weak state; real values on self-adjoint observables are preserved. -/
def positivePart (τ : TracialState A) : A →ₚ[ℂ] ℂ where
  toLinearMap := (hermitianPart τ).toLinearMap
  monotone' := by
    intro a b hab
    change (hermitianPart τ).toLinearMap a≤(hermitianPart τ).toLinearMap b
    apply sub_nonneg.mp
    rw [←map_sub]
    obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hab)
    rw [hz]
    exact hermitianPart_square_nonneg τ z

abbrev TracialGNS (τ : TracialState A) := (positivePart τ).GNS

def representation (τ : TracialState A) : A →⋆ₐ[ℂ] (TracialGNS τ →L[ℂ] TracialGNS τ) :=
  (positivePart τ).gnsStarAlgHom

def cyclicVector (τ : TracialState A) : TracialGNS τ :=
  ((positivePart τ).toPreGNS (1:A) : (positivePart τ).GNS)

theorem representation_cyclicVector (τ : TracialState A) (a : A) :
    representation τ a (cyclicVector τ)=
      ((positivePart τ).toPreGNS a : (positivePart τ).GNS) := by
  change (positivePart τ).gnsNonUnitalStarAlgHom a ((positivePart τ).toPreGNS 1)=_
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  simp

theorem vector_coefficient (τ : TracialState A) (a : A) :
    inner ℂ (cyclicVector τ) (representation τ a (cyclicVector τ))=
      (hermitianPart τ).toLinearMap a := by
  rw [representation_cyclicVector]
  change inner ℂ ((positivePart τ).toPreGNS 1 : (positivePart τ).GNS)
    ((positivePart τ).toPreGNS a : (positivePart τ).GNS)=_
  rw [UniformSpace.Completion.inner_coe,PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,star_one,one_mul]
  rfl

theorem cyclicVector_norm_sq (τ : TracialState A) : ‖cyclicVector τ‖^2=1 := by
  have h := congrArg Complex.re (vector_coefficient τ (1:A))
  simp only [map_one,one_apply_eq_self,(hermitianPart τ).normalized,Complex.one_re] at h
  exact (inner_self_eq_norm_sq (𝕜:=ℂ) (cyclicVector τ)).symm.trans h

theorem denseRange_cyclic (τ : TracialState A) :
    DenseRange (fun a : A => representation τ a (cyclicVector τ)) := by
  simp only [representation_cyclicVector]
  exact UniformSpace.Completion.denseRange_coe.comp (positivePart τ).toPreGNS.surjective.denseRange (UniformSpace.Completion.continuous_coe _)

theorem preGNS_star_norm (τ : TracialState A) (a : A) :
    ‖(positivePart τ).toPreGNS (star a)‖=‖(positivePart τ).toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
  change Real.sqrt ((hermitianPart τ).toLinearMap (a*star a)).re=
    Real.sqrt ((hermitianPart τ).toLinearMap (star a*a)).re
  rw [(hermitianPart τ).cyclic]

theorem right_mul_norm (τ : TracialState A) (a b : A) :
    ‖representation τ (a*b) (cyclicVector τ)‖≤‖b‖*‖representation τ a (cyclicVector τ)‖ := by
  simp only [representation_cyclicVector,UniformSpace.Completion.norm_coe]
  rw [←preGNS_star_norm τ (a*b),star_mul]
  have h := (positivePart τ).leftMulMapPreGNS (star b) |>.le_opNorm ((positivePart τ).toPreGNS (star a))
  have h' : ‖(positivePart τ).leftMulMapPreGNS (star b)‖≤‖star b‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    apply LinearMap.mkContinuous_norm_le _ (norm_nonneg _)
  have h'' := le_trans h (mul_le_mul_of_nonneg_right h' (norm_nonneg _))
  simpa only [PositiveLinearMap.leftMulMapPreGNS_apply,PositiveLinearMap.ofPreGNS_toPreGNS,
    norm_star,preGNS_star_norm] using h''

/-- The closed image is a C*-algebra even without an a priori closed-range API. -/
def gnsClosure (τ : TracialState A) : StarSubalgebra ℂ (TracialGNS τ →L[ℂ] TracialGNS τ) :=
  (representation τ).range.topologicalClosure

instance gnsClosure_isClosed (τ : TracialState A) :
    IsClosed (gnsClosure τ : Set (TracialGNS τ →L[ℂ] TracialGNS τ)) :=
  (representation τ).range.isClosed_topologicalClosure

abbrev FaithfulGNSAlgebra (τ : TracialState A) := gnsClosure τ


def quotientMap (τ : TracialState A) : A →⋆ₐ[ℂ] FaithfulGNSAlgebra τ :=
  (representation τ).codRestrict (gnsClosure τ) (fun a => subset_closure ⟨a,rfl⟩)

def operatorCoefficient (τ : TracialState A) : (TracialGNS τ →L[ℂ] TracialGNS τ) →ₗ[ℂ] ℂ where
  toFun T := inner ℂ (cyclicVector τ) (T (cyclicVector τ))
  map_add' T S := by simp only [ContinuousLinearMap.add_apply,inner_add_right]
  map_smul' c T := by simp only [ContinuousLinearMap.smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply]

theorem operatorCoefficient_continuous (τ : TracialState A) : Continuous (operatorCoefficient τ) := by
  change Continuous (fun T : TracialGNS τ →L[ℂ] TracialGNS τ => inner ℂ (cyclicVector τ) (T (cyclicVector τ)))
  fun_prop

theorem closure_cyclic (τ : TracialState A) (T S : TracialGNS τ →L[ℂ] TracialGNS τ)
    (hT : T∈gnsClosure τ) (hS : S∈gnsClosure τ) :
    operatorCoefficient τ (T*S)=operatorCoefficient τ (S*T) := by
  have hfixed (b : A) (T : TracialGNS τ →L[ℂ] TracialGNS τ) (hT : T∈gnsClosure τ) :
      operatorCoefficient τ (T*representation τ b)=operatorCoefficient τ (representation τ b*T) := by
    have hc : IsClosed {T | operatorCoefficient τ (T*representation τ b)=operatorCoefficient τ (representation τ b*T)} :=
      isClosed_eq ((operatorCoefficient_continuous τ).comp (continuous_id.mul_const _))
        ((operatorCoefficient_continuous τ).comp (continuous_id.const_mul _))
    apply (closure_minimal ?_ hc) hT
    rintro T ⟨a,rfl⟩
    change inner ℂ (cyclicVector τ) ((representation τ a*representation τ b) (cyclicVector τ))=_
    rw [←map_mul,vector_coefficient]
    change _=inner ℂ (cyclicVector τ) ((representation τ b*representation τ a) (cyclicVector τ))
    rw [←map_mul,vector_coefficient,(hermitianPart τ).cyclic]
  have hc : IsClosed {S | operatorCoefficient τ (T*S)=operatorCoefficient τ (S*T)} :=
    isClosed_eq ((operatorCoefficient_continuous τ).comp (continuous_id.const_mul _))
      ((operatorCoefficient_continuous τ).comp (continuous_id.mul_const _))
  apply (closure_minimal ?_ hc) hS
  rintro S ⟨b,rfl⟩
  exact hfixed b T hT

theorem closure_right_mul_norm (τ : TracialState A) (T : TracialGNS τ →L[ℂ] TracialGNS τ)
    (hT : T∈gnsClosure τ) (b : A) :
    ‖T (representation τ b (cyclicVector τ))‖≤‖b‖*‖T (cyclicVector τ)‖ := by
  have hc : IsClosed {T : TracialGNS τ →L[ℂ] TracialGNS τ |
      ‖T (representation τ b (cyclicVector τ))‖≤‖b‖*‖T (cyclicVector τ)‖} := by
    apply isClosed_le <;> fun_prop
  apply (closure_minimal ?_ hc) hT
  rintro T ⟨a,rfl⟩
  change ‖representation τ a (representation τ b (cyclicVector τ))‖≤‖b‖*‖representation τ a (cyclicVector τ)‖
  simpa only [map_mul,ContinuousLinearMap.mul_apply] using right_mul_norm τ a b

theorem closure_separating (τ : TracialState A) (T : TracialGNS τ →L[ℂ] TracialGNS τ)
    (hT : T∈gnsClosure τ) (hzero : T (cyclicVector τ)=0) : T=0 := by
  have h (a : A) : T (representation τ a (cyclicVector τ))=0 := by
    have hn := closure_right_mul_norm τ T hT a
    rw [hzero,norm_zero,mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have hz := (denseRange_cyclic τ).equalizer T.continuous (continuous_const (y:=(0:TracialGNS τ))) (funext h)
  ext x
  exact congr_fun hz x

def quotientState (τ : TracialState A) : TracialState (FaithfulGNSAlgebra τ) where
  toLinearMap := (operatorCoefficient τ).comp (gnsClosure τ).subtype.toLinearMap
  normalized := by
    change inner ℂ (cyclicVector τ) (cyclicVector τ)=1
    simpa only [map_one,one_apply_eq_self,(hermitianPart τ).normalized] using vector_coefficient τ (1:A)
  positive T := by
    change 0≤(inner ℂ (cyclicVector τ) ((star (T:TracialGNS τ →L[ℂ] TracialGNS τ)*T) (cyclicVector τ))).re
    rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_nonneg (𝕜:=ℂ) (x:=(T:TracialGNS τ →L[ℂ] TracialGNS τ) (cyclicVector τ))
  cyclic T S := closure_cyclic τ T S T.property S.property

theorem quotientState_preserves (τ : TracialState A) (a : A) :
    (quotientState τ).toLinearMap (quotientMap τ a)=(hermitianPart τ).toLinearMap a :=
  vector_coefficient τ a

theorem quotientState_faithful (τ : TracialState A) (T : FaithfulGNSAlgebra τ)
    (h : (quotientState τ).toLinearMap (star T*T)=0) : T=0 := by
  change inner ℂ (cyclicVector τ) ((star (T:TracialGNS τ →L[ℂ] TracialGNS τ)*T) (cyclicVector τ))=0 at h
  rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_zero] at h
  apply Subtype.ext
  exact closure_separating τ T T.property h

open scoped ComplexOrder in
 theorem quotientState_square_nonneg (τ : TracialState A) (T : FaithfulGNSAlgebra τ) :
    0≤(quotientState τ).toLinearMap (star T*T) := by
  change 0 ≤ inner ℂ (cyclicVector τ) ((star (T:TracialGNS τ →L[ℂ] TracialGNS τ)*T) (cyclicVector τ))
  rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact Complex.nonneg_iff.mpr ⟨inner_self_nonneg (𝕜:=ℂ), (inner_self_im (𝕜:=ℂ) _).symm⟩

theorem quotientState_star (τ : TracialState A) (T : FaithfulGNSAlgebra τ) :
    (quotientState τ).toLinearMap (star T)=star ((quotientState τ).toLinearMap T) := by
  change inner ℂ (cyclicVector τ) ((star (T:TracialGNS τ →L[ℂ] TracialGNS τ)) (cyclicVector τ))=
    star (inner ℂ (cyclicVector τ) ((T:TracialGNS τ →L[ℂ] TracialGNS τ) (cyclicVector τ)))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜:=ℂ) ((T:TracialGNS τ →L[ℂ] TracialGNS τ) (cyclicVector τ)) (cyclicVector τ)).symm

end
end E2.ExactTrace
