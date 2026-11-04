import E2.FiniteMatrixTools
import Mathlib.Logic.Equiv.Fin.Rotate

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

abbrev Bits (N : ℕ) := Fin N → Bool

def rotateWord (N : ℕ) : Equiv.Perm (Bits N) where
  toFun b j := b (finRotate N j)
  invFun b j := b ((finRotate N).symm j)
  left_inv b := by
    funext j
    exact congrArg b ((finRotate N).apply_symm_apply j)
  right_inv b := by
    funext j
    exact congrArg b ((finRotate N).symm_apply_apply j)

def flipWord {N : ℕ} (j : Fin N) : Equiv.Perm (Bits N) where
  toFun b := Function.update b j (!b j)
  invFun b := Function.update b j (!b j)
  left_inv b := by funext i; by_cases h : i=j <;> simp [h]
  right_inv b := by funext i; by_cases h : i=j <;> simp [h]

def bit {N : ℕ} (b : Bits N) (j : Fin N) : ℝ := if b j then 1 else 0

def coefficient (j : ℕ) : ℝ := 3*(1/4:ℝ)^(j+1)

def coordinate {N : ℕ} (b : Bits N) : ℝ := ∑ j, coefficient j.val*bit b j

theorem bit_bounds {N : ℕ} (b : Bits N) (j : Fin N) : 0≤bit b j ∧ bit b j≤1 := by
  cases h : b j <;> simp [bit,h]

theorem coefficient_nonneg (j : ℕ) : 0≤coefficient j := by unfold coefficient; positivity

theorem coefficient_sum (N : ℕ) : (∑ j : Fin N, coefficient j.val)=1-(1/4:ℝ)^N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc]
    rw [ih]
    simp only [coefficient,Fin.val_last,pow_succ]
    ring

theorem coordinate_bounds {N : ℕ} (b : Bits N) : 0≤coordinate b ∧ coordinate b≤1 := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (coefficient_nonneg _) (bit_bounds b j).1)
  · calc
      _ ≤ ∑ j : Fin N, coefficient j.val := Finset.sum_le_sum (fun j _ => by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (bit_bounds b j).2 (coefficient_nonneg _))
      _ = 1-(1/4:ℝ)^N := coefficient_sum N
      _ ≤ 1 := by
        have : 0≤(1/4:ℝ)^N := by positivity
        linarith

theorem rotated_coefficient (n : ℕ) (j : Fin (n+1)) :
    coefficient ((finRotate (n+1)).symm j).val-4*coefficient j.val=
      if j=0 then 3*(1/4:ℝ)^(n+1)-3 else 0 := by
  by_cases hj : j=0
  · subst j
    have hlast : (finRotate (n+1)).symm 0=Fin.last n := by
      apply (finRotate (n+1)).symm_apply_eq.mpr
      exact finRotate_last.symm
    norm_num [hlast,coefficient]
  · rw [if_neg hj,coe_finRotate_symm_of_ne_zero hj]
    have hjpos : 0<j.val := by exact Fin.pos_iff_ne_zero.mpr hj
    unfold coefficient
    rw [show j.val-1+1=j.val by omega]
    simp only [pow_succ]
    ring

theorem rotate_coordinate (n : ℕ) (b : Bits (n+1)) :
    coordinate (rotateWord (n+1) b)-4*coordinate b+3*bit b 0=
      3*(1/4:ℝ)^(n+1)*bit b 0 := by
  have hs : coordinate (rotateWord (n+1) b)=
      ∑ j, coefficient ((finRotate (n+1)).symm j).val*bit b j := by
    rw [coordinate]
    convert Equiv.sum_comp (finRotate (n+1)) (fun j => coefficient ((finRotate (n+1)).symm j).val*bit b j) using 1
    simp [bit,rotateWord]
  rw [hs,coordinate,Finset.mul_sum,←Finset.sum_sub_distrib]
  have he : (∑ j : Fin (n+1), (coefficient ((finRotate (n+1)).symm j).val*bit b j-
      4*(coefficient j.val*bit b j)))=(3*(1/4:ℝ)^(n+1)-3)*bit b 0 := by
    calc
      _ = ∑ j : Fin (n+1), (coefficient ((finRotate (n+1)).symm j).val-4*coefficient j.val)*bit b j := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp_rw [rotated_coefficient]; simp
  rw [he]
  ring

theorem flip_bit_same {N : ℕ} (b : Bits N) (j : Fin N) :
    bit (flipWord j b) j=1-bit b j := by
  cases h : b j <;> simp [bit,flipWord,h]

theorem flip_bit_other {N : ℕ} (b : Bits N) (i j : Fin N) (h : i≠j) :
    bit (flipWord j b) i=bit b i := by
  simp [bit,flipWord,h]

theorem flip_coordinate {N : ℕ} (b : Bits N) (j : Fin N) :
    coordinate (flipWord j b)-coordinate b=coefficient j.val*(1-2*bit b j) := by
  rw [coordinate,coordinate,←Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · rw [flip_bit_same]
    ring
  · intro i hi hij
    rw [flip_bit_other b i j hij]
    ring
  · simp


theorem rotate_flip_coordinate (n : ℕ) (b : Bits (n+1)) :
    coordinate (rotateWord (n+1) (flipWord 0 b))-coordinate (rotateWord (n+1) b)=
      3*(1/4:ℝ)^(n+1)*(1-2*bit b 0) := by
  have h1 := rotate_coordinate n (flipWord 0 b)
  have h2 := rotate_coordinate n b
  have hf := flip_coordinate b (0:Fin (n+1))
  rw [flip_bit_same] at h1
  norm_num [coefficient] at hf
  nlinarith

end
end E2.FiniteConstruction
