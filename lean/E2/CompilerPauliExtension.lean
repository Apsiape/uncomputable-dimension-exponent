import E2.CompilerTensorSource

namespace E2.CompilerTensor
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open E2.FiniteConstruction
variable {κ : Type*} [Fintype κ]
local instance : DecidableEq κ := Classical.decEq κ

abbrev Register (κ : Type*) := κ → Bool

def bitFlip (i : κ) : Equiv.Perm (Register κ) where
  toFun a := Function.update a i (!(a i))
  invFun a := Function.update a i (!(a i))
  left_inv a := by funext j; by_cases h : j=i <;> simp [h]
  right_inv a := by funext j; by_cases h : j=i <;> simp [h]

def rawX (i : κ) : Matrix (Register κ) (Register κ) ℂ := (bitFlip i).permMatrix ℂ

def rawZ (i : κ) : Matrix (Register κ) (Register κ) ℂ :=
  Matrix.diagonal (fun a => if a i then 1 else -1)

theorem rawX_star (i : κ) : (rawX i).conjTranspose=rawX i := by
  rw [rawX,Matrix.conjTranspose_permMatrix]
  rfl

theorem rawX_square (i : κ) : rawX i*rawX i=1 := by
  have h := (perm_unitary (bitFlip i)).1
  change (rawX i).conjTranspose*rawX i=1 at h
  rw [rawX_star] at h
  exact h

theorem rawZ_star (i : κ) : (rawZ i).conjTranspose=rawZ i := by
  ext a b
  by_cases h : a=b
  · subst b
    cases ha : a i <;> simp [rawZ,Matrix.conjTranspose_apply,ha]
  · simp [rawZ,Matrix.conjTranspose_apply,h,Ne.symm h]

theorem rawZ_square (i : κ) : rawZ i*rawZ i=1 := by
  rw [rawZ,Matrix.diagonal_mul_diagonal]
  have he : (fun a : Register κ => (if a i then (1:ℂ) else -1)*(if a i then 1 else -1))=fun _ => 1 := by
    funext a
    cases a i <;> norm_num
  rw [he,Matrix.diagonal_one]

theorem rawXX (i j : κ) : rawX i*rawX j=rawX j*rawX i := by
  have he : bitFlip i*bitFlip j=bitFlip j*bitFlip i := by
    ext a k
    by_cases hij : i=j
    · subst j; rfl
    · by_cases hki : k=i <;> by_cases hkj : k=j <;>
        simp_all [bitFlip,Function.update_apply]
  simp only [rawX,← Matrix.permMatrix_mul,he]

theorem rawZZ (i j : κ) : rawZ i*rawZ j=rawZ j*rawZ i := by
  simp only [rawZ,Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

theorem rawXZ_conjugate (i j : κ) :
    rawX i*rawZ j*rawX i=if i=j then -rawZ j else rawZ j := by
  have hc := perm_conj_diagonal (bitFlip i) (fun a : Register κ => if a j then (1:ℂ) else -1)
  change rawX i*rawZ j*(rawX i).conjTranspose=_ at hc
  rw [rawX_star] at hc
  rw [hc]
  by_cases hij : i=j
  · subst j
    simp only [ite_true]
    ext a b
    by_cases hab : a=b
    · subst b
      cases ha : a i <;> simp [rawZ,bitFlip,ha]
    · simp [rawZ,hab]
  · simp only [ite_eq_right hij]
    congr 1
    funext a
    simp [bitFlip,Function.update_of_ne (Ne.symm hij)]

def registerMatrix (M : Matrix (Register κ) (Register κ) ℂ) : Mat (Fintype.card (Register κ)) :=
  matrixReindexStar (Fintype.equivFin (Register κ)) M

def pauliX (i : κ) : Mat (Fintype.card (Register κ)) := registerMatrix (rawX i)
def pauliZ (i : κ) : Mat (Fintype.card (Register κ)) := registerMatrix (rawZ i)

theorem pauliX_domain (i : κ) : Domain.reflection.Holds (pauliX i) := by
  constructor
  · exact congrArg registerMatrix (rawX_star i)
  · simpa only [pauliX,registerMatrix,map_mul,map_one] using congrArg registerMatrix (rawX_square i)

theorem pauliZ_domain (i : κ) : Domain.reflection.Holds (pauliZ i) := by
  constructor
  · exact congrArg registerMatrix (rawZ_star i)
  · simpa only [pauliZ,registerMatrix,map_mul,map_one] using congrArg registerMatrix (rawZ_square i)

theorem pauliXX (i j : κ) : Commute (pauliX i) (pauliX j) := by
  change pauliX i*pauliX j=pauliX j*pauliX i
  simpa only [pauliX,registerMatrix,map_mul] using congrArg registerMatrix (rawXX i j)

theorem pauliZZ (i j : κ) : Commute (pauliZ i) (pauliZ j) := by
  change pauliZ i*pauliZ j=pauliZ j*pauliZ i
  simpa only [pauliZ,registerMatrix,map_mul] using congrArg registerMatrix (rawZZ i j)

theorem pauliXZ_conjugate (i j : κ) :
    pauliX i*pauliZ j*pauliX i=if i=j then -pauliZ j else pauliZ j := by
  simpa only [pauliX,pauliZ,registerMatrix,map_mul,map_neg,apply_ite] using
    congrArg registerMatrix (rawXZ_conjugate i j)

theorem register_dimension : 0 < Fintype.card (Register κ) := Fintype.card_pos

end
end E2.CompilerTensor
