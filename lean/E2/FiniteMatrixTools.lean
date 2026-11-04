import E2.Weighted
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

def flatState (d : ℕ) (hd : 0<d) : State d where
  rho := ((d:ℂ)⁻¹) • 1
  positive := Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
    exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le d)))
  normalized := by
    simp only [Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hd))
  xi := (((Real.sqrt (d:ℝ))⁻¹:ℝ):ℂ) • 1
  xi_positive := Matrix.PosSemidef.smul Matrix.PosSemidef.one (by
    exact_mod_cast inv_nonneg.mpr (Real.sqrt_nonneg (d:ℝ)))
  xi_square := by
    rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
    congr 1
    push_cast
    rw [←mul_inv_rev]
    congr 1
    exact_mod_cast (Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ d))

theorem flatState_commutes {d : ℕ} (hd : 0<d) (a : Mat d) :
    comm a (flatState d hd).xi=0 := by
  simp [comm,Companion.Analytic.comm,flatState,Matrix.mul_smul,Matrix.smul_mul]

theorem state_hs_one {d : ℕ} (s : State d) : hs s.xi=1 := by
  have h : hs s.xi^2=1 := by
    rw [hsNorm_sq,hsSquared_trace,s.xi_positive.isHermitian.eq,s.xi_square,s.normalized]
    norm_num
  nlinarith [hsNorm_nonneg s.xi]

theorem weighted_le_norm {d : ℕ} (s : State d) (a : Mat d) : weighted s a ≤ ‖a‖ := by
  simpa only [weighted,state_hs_one s,mul_one] using operator_mul_hs a s.xi

theorem perm_unitary {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    (σ.permMatrix ℂ).conjTranspose*σ.permMatrix ℂ=1 ∧
    σ.permMatrix ℂ*(σ.permMatrix ℂ).conjTranspose=1 := by
  simp only [Matrix.conjTranspose_permMatrix,←Matrix.permMatrix_mul,
    mul_inv_cancel,inv_mul_cancel,Matrix.permMatrix_one,and_self]

theorem perm_conj_diagonal {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (v : α → ℂ) :
    σ.permMatrix ℂ*Matrix.diagonal v*(σ.permMatrix ℂ).conjTranspose=
      Matrix.diagonal (fun i => v (σ i)) := by
  rw [Matrix.conjTranspose_permMatrix]
  change σ.toPEquiv.toMatrix*Matrix.diagonal v*(σ⁻¹).toPEquiv.toMatrix=_
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  change Matrix.diagonal v (σ i) (σ j)=Matrix.diagonal (fun i => v (σ i)) i j
  by_cases h : i=j
  · subst j; simp
  · simp [Matrix.diagonal_apply,h,σ.injective.ne h]

theorem diagonal_projection {α : Type*} [Fintype α] [DecidableEq α] (b : α → Bool) :
    (Matrix.diagonal (fun i => if b i then (1:ℂ) else 0)).conjTranspose=
      Matrix.diagonal (fun i => if b i then (1:ℂ) else 0) ∧
    Matrix.diagonal (fun i => if b i then (1:ℂ) else 0)*
      Matrix.diagonal (fun i => if b i then (1:ℂ) else 0)=
      Matrix.diagonal (fun i => if b i then (1:ℂ) else 0) := by
  constructor
  · ext i j
    by_cases h : i=j
    · subst j
      cases hb : b i <;> simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,hb]
    · simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    cases b i <;> simp

theorem diagonal_positive_contraction {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → ℝ) (hv : ∀ i, 0≤v i ∧ v i≤1) :
    (Matrix.diagonal (fun i => (v i:ℂ))).PosSemidef ∧
      (1-Matrix.diagonal (fun i => (v i:ℂ))).PosSemidef := by
  constructor
  · rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast (hv i).1
  · rw [show (1:Matrix α α ℂ)=Matrix.diagonal (fun _ => 1) by simp,Matrix.diagonal_sub,
      Matrix.posSemidef_diagonal_iff]
    intro i
    change 0 ≤ 1-(v i:ℂ)
    exact sub_nonneg.mpr (by exact_mod_cast (hv i).2)


theorem perm_comm_diagonal_norm {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (v : α → ℂ) (ε : ℝ) (hε : 0≤ε)
    (hv : ∀ i, ‖v (σ i)-v i‖≤ε) :
    ‖σ.permMatrix ℂ*Matrix.diagonal v-Matrix.diagonal v*σ.permMatrix ℂ‖≤ε := by
  have he : σ.permMatrix ℂ*Matrix.diagonal v-Matrix.diagonal v*σ.permMatrix ℂ=
      (σ.permMatrix ℂ*Matrix.diagonal v*(σ.permMatrix ℂ).conjTranspose-Matrix.diagonal v)*σ.permMatrix ℂ := by
    rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_assoc,(perm_unitary σ).1,Matrix.mul_one]
  rw [he,perm_conj_diagonal,Matrix.diagonal_sub]
  calc
    _ ≤ ‖Matrix.diagonal (fun i => v (σ i)-v i)‖*‖σ.permMatrix ℂ‖ := norm_mul_le _ _
    _ ≤ ε*1 := mul_le_mul (by rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hε).mpr hv)
      (Matrix.permMatrix_l2_opNorm_le σ) (norm_nonneg _) hε
    _ = ε := mul_one _

end
end E2.FiniteConstruction
