import E2.MomentUltralimit
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Matrix.Order

namespace E2.ExactCompactness
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Companion.Analytic
set_option linter.unusedSimpArgs false

theorem state_hs_xi {d : ℕ} (s : State d) : hs s.xi=1 := by
  have h : hs s.xi^2=1 := by
    rw [hsNorm_sq,hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
    norm_num
  nlinarith [hsNorm_nonneg s.xi]

theorem projection_expectation_eq {d : ℕ} (s : State d) (F : Mat d)
    (hF : Domain.projection.Holds F) : expectation s F=hs (F*s.xi)^2 := by
  rw [hs_square_gram,hF.1,hF.2,s.xi_positive.isHermitian.eq]
  unfold expectation
  rw [Matrix.trace_mul_cycle,s.xi_square]

def matrixStateLinear {d : ℕ} (s : State d) : Mat d →ₗ[ℂ] ℂ where
  toFun a := Matrix.trace (s.rho*a)
  map_add' a b := by simp [Matrix.mul_add]
  map_smul' c a := by simp [Matrix.mul_smul]

theorem matrixState_sandwich {d : ℕ} (s : State d) (a : Mat d) :
    matrixStateLinear s a=Matrix.trace (s.xi*a*s.xi) := by
  change Matrix.trace (s.rho*a)=_
  rw [Matrix.trace_mul_cycle,s.xi_square]

def matrixStatePositive {d : ℕ} (s : State d) : Mat d →ₚ[ℂ] ℂ :=
  .mk₀ (matrixStateLinear s) (by
    intro a ha
    rw [matrixState_sandwich]
    have hpa : a.PosSemidef := by
      change (a-0).PosSemidef at ha
      simpa only [sub_zero] using ha
    have h := hpa.mul_mul_conjTranspose_same s.xi
    simpa only [s.xi_positive.isHermitian.eq] using h.trace_nonneg)

theorem matrixState_one {d : ℕ} (s : State d) : matrixStateLinear s 1=1 := by
  change Matrix.trace (s.rho*1)=1
  rw [Matrix.mul_one,s.normalized]

theorem matrixState_star {d : ℕ} (s : State d) (a : Mat d) :
    matrixStateLinear s (star a)=star (matrixStateLinear s a) := by
  rw [matrixState_sandwich,matrixState_sandwich,←Matrix.trace_conjTranspose]
  simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq,Matrix.mul_assoc]

theorem positive_normalized_bound_four {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (φ : A →ₚ[ℂ] ℂ) (h1 : φ 1=1) (a : A) : ‖φ a‖≤4*‖a‖ := by
  obtain ⟨x,hx,hn,he⟩ := CStarAlgebra.exists_sum_four_nonneg a
  calc
    ‖φ a‖=‖∑ i : Fin 4, Complex.I^i.val • φ (x i)‖ := by rw [he,map_sum]; simp only [map_smul]
    _≤∑ i : Fin 4, ‖φ (x i)‖ := by
      convert norm_sum_le (Finset.univ) (fun i : Fin 4 => Complex.I^i.val • φ (x i)) using 1 <;> simp [norm_smul]
    _≤∑ _i : Fin 4, ‖a‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := φ.norm_apply_le_of_nonneg (x i) (hx i)
      simpa only [h1,norm_one,one_mul] using hh.trans (by simpa only [h1,norm_one,one_mul] using hn i)
    _=4*‖a‖ := by simp

theorem matrixState_bound {d : ℕ} (s : State d) (a : Mat d) : ‖matrixStateLinear s a‖≤4*‖a‖ :=
  positive_normalized_bound_four (matrixStatePositive s) (matrixState_one s) a

theorem matrixState_square {d : ℕ} (s : State d) (a : Mat d) :
    (matrixStateLinear s (star a*a)).re=weighted s a^2 := by
  rw [matrixState_sandwich]
  simp only [weighted,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_mul,
    s.xi_positive.isHermitian.eq,Matrix.star_eq_conjTranspose,Matrix.mul_assoc]

def hsVector {d : ℕ} (a : Mat d) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij => a ij.1 ij.2)

theorem hsVector_norm {d : ℕ} (a : Mat d) : ‖hsVector a‖=hs a := by
  apply (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg _)).mp
  simp only [hsVector,EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,hsNorm_sq,hsSquared,Complex.normSq_eq_norm_sq]

theorem hsVector_inner {d : ℕ} (a b : Mat d) :
    inner ℂ (hsVector a) (hsVector b)=Matrix.trace (a.conjTranspose*b) := by
  simp only [hsVector,PiLp.inner_apply,PiLp.toLp_apply,RCLike.inner_apply',starRingEnd_apply,
    Fintype.sum_prod_type,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem trace_mul_hs_bound {d : ℕ} (a b : Mat d) : ‖Matrix.trace (a*b)‖≤hs a*hs b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (hsVector a.conjTranspose) (hsVector b)
  simpa only [hsVector_inner,hsVector_norm,Matrix.conjTranspose_conjTranspose,hsNorm_conjTranspose] using h

theorem matrixState_square_complex {d : ℕ} (s : State d) (a : Mat d) :
    matrixStateLinear s (star a*a)=Complex.ofReal (weighted s a^2) := by
  have hp : 0≤matrixStateLinear s (star a*a) :=
    (matrixStatePositive s).map_nonneg (star_mul_self_nonneg a)
  apply Complex.ext
  · exact matrixState_square s a
  · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hp).2.symm

theorem matrixState_cyclic_error {d : ℕ} (s : State d) (X Y : Mat d) :
    ‖matrixStateLinear s (X*Y)-matrixStateLinear s (Y*X)‖≤2*hs (comm X s.xi)*‖Y‖ := by
  let C := comm X s.xi
  have he : s.rho*X-X*s.rho=-(s.xi*C+C*s.xi) := by
    rw [←s.xi_square]
    dsimp only [C,comm,Companion.Analytic.comm]
    noncomm_ring
  have ht : matrixStateLinear s (X*Y)-matrixStateLinear s (Y*X)=Matrix.trace ((s.rho*X-X*s.rho)*Y) := by
    change Matrix.trace (s.rho*(X*Y))-Matrix.trace (s.rho*(Y*X))=_
    simp only [Matrix.sub_mul,Matrix.trace_sub,Matrix.mul_assoc]
    rw [Matrix.trace_mul_cycle' X s.rho Y,Matrix.trace_mul_cycle' Y X s.rho]
  rw [ht,he,Matrix.neg_mul,Matrix.trace_neg,norm_neg,Matrix.add_mul,Matrix.trace_add]
  calc
    _≤‖Matrix.trace (s.xi*C*Y)‖+‖Matrix.trace (C*s.xi*Y)‖ := norm_add_le _ _
    _≤hs s.xi*hs (C*Y)+hs C*hs (s.xi*Y) := by
      simp only [Matrix.mul_assoc]
      exact add_le_add (trace_mul_hs_bound _ _) (trace_mul_hs_bound _ _)
    _≤hs C*‖Y‖+hs C*‖Y‖ := by
      rw [state_hs_xi,one_mul]
      have h0 := hs_mul_operator C Y
      have h1 := hs_mul_operator s.xi Y
      rw [state_hs_xi,one_mul] at h1
      exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 (hsNorm_nonneg _))
    _=2*hs (comm X s.xi)*‖Y‖ := by ring

theorem matrix_domain_to_exact {d : ℕ} (D : Domain) (a : Mat d) (ha : D.Holds a) : D.HoldsC a := by
  cases D with
  | positiveContraction =>
    apply positive_of_norms
    · exact ha.1.isHermitian.isSelfAdjoint
    · exact positive_contraction_norm ha
    · exact positive_contraction_norm ⟨ha.2,by simpa using ha.1⟩
  | projection => exact ha
  | reflection => exact ha
  | unitary => exact ha

theorem matrix_domain_norm {d : ℕ} (hd : 0<d) (D : Domain) (a : Mat d) (ha : D.Holds a) : ‖a‖≤1 := by
  cases D with
  | positiveContraction => exact positive_contraction_norm ha
  | projection => exact projection_norm_le ha
  | reflection => exact (unitary_norm hd (reflection_unitary _ ha)).le
  | unitary => exact (unitary_norm hd ha).le

end
end E2.ExactCompactness
