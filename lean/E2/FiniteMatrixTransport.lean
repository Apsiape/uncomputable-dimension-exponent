import E2.FiniteMatrixTools
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace E2.FiniteConstruction
noncomputable section
open scoped Matrix.Norms.L2Operator

def matrixReindexStar {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) : Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ where
  __ := Matrix.reindexAlgEquiv ℂ ℂ e
  map_star' a := rfl
  map_smul' c a := rfl

theorem matrixReindex_norm {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a : Matrix α α ℂ) : ‖matrixReindexStar e a‖=‖a‖ :=
  StarAlgEquiv.norm_map _ _

theorem permutation_conjugation_norm {α : Type*} [Fintype α] [DecidableEq α]
    (s : Equiv.Perm α) (a : Matrix α α ℂ) :
    ‖s.permMatrix ℂ*a*(s.permMatrix ℂ).conjTranspose‖ ≤ ‖a‖ := by
  have hs : ‖s.permMatrix ℂ‖≤1 := Matrix.permMatrix_l2_opNorm_le _
  have ht : ‖(s.permMatrix ℂ).conjTranspose‖≤1 := by
    rw [Matrix.conjTranspose_permMatrix]
    exact Matrix.permMatrix_l2_opNorm_le _
  calc
    _ ≤ (‖s.permMatrix ℂ‖*‖a‖)*‖(s.permMatrix ℂ).conjTranspose‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖a‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) ht (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

end
end E2.FiniteConstruction