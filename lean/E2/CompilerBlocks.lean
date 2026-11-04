import E2.CompilerGadgets
import Mathlib.LinearAlgebra.Matrix.Notation

namespace E2.CompilerBlocks
variable {A : Type*} [Ring A]
abbrev Block (A : Type*) := Matrix (Fin 2) (Fin 2) A

def diag (a b : A) : Block A := !![a,0;0,b]
def off (a b : A) : Block A := !![0,a;b,0]

@[simp] theorem diag_mul_diag (a b c d : A) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem diag_mul_off (a b c d : A) : diag a b * off c d = off (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,off,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem off_mul_diag (a b c d : A) : off a b * diag c d = off (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,off,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem off_mul_off (a b c d : A) : off a b * off c d = diag (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,off,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem diag_one : diag (1 : A) 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]

variable [StarRing A]

@[simp] theorem star_diag (a b : A) : star (diag a b) = diag (star a) (star b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
@[simp] theorem star_off (a b : A) : star (off a b) = off (star b) (star a) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [off,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

def Reflection (a : A) : Prop := star a=a ∧ a*a=1

theorem reflection_one : Reflection (1 : A) := by simp [Reflection]

theorem reflection_diag {a b : A} (ha : Reflection a) (hb : Reflection b) :
    Reflection (diag a b) := by
  constructor <;> simp [ha.1,hb.1,ha.2,hb.2]

theorem reflection_off {a : A} (ha : Reflection a) : Reflection (off a a) := by
  constructor <;> simp [ha.1,ha.2]

theorem reflection_conjugate {a b : A} (ha : Reflection a) (hb : Reflection b) :
    Reflection (a*b*a) := by
  constructor
  · simp [star_mul,ha.1,hb.1,mul_assoc]
  · calc
      _ = a*b*(a*a)*b*a := by simp only [mul_assoc]
      _ = a*(b*b)*a := by rw [ha.2,mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [hb.2,mul_one,ha.2]

theorem reflection_product {a b : A} (ha : Reflection a) (hb : Reflection b)
    (hcomm : a*b=b*a) : Reflection (a*b) := by
  constructor
  · simpa only [star_mul,ha.1,hb.1] using hcomm.symm
  · calc
      _ = a*(b*a)*b := by simp only [mul_assoc]
      _ = a*(a*b)*b := by rw [hcomm]
      _ = 1 := by rw [← mul_assoc a a b,ha.2,one_mul,hb.2]

def ParityTriple (a b c : A) : Prop :=
  a*b=b*a ∧ a*c=c*a ∧ b*c=c*b ∧ a*b*c=1

theorem parity_of_product {a b c : A} (ha : Reflection a) (hb : Reflection b)
    (hc : Reflection c) (hprod : a*b=c) : ParityTriple a b c := by
  have hba : b*a=c := by
    have h := congrArg star hprod
    simpa only [star_mul,ha.1,hb.1,hc.1] using h
  have hab : a*b=b*a := hprod.trans hba.symm
  have hac : a*c=c*a := by
    calc
      _ = a*(a*b) := by rw [hprod]
      _ = b := by rw [← mul_assoc,ha.2,one_mul]
      _ = (b*a)*a := by rw [mul_assoc,ha.2,mul_one]
      _ = c*a := by rw [hba]
  have hbc : b*c=c*b := by
    calc
      _ = b*(b*a) := by rw [hba]
      _ = a := by rw [← mul_assoc,hb.2,one_mul]
      _ = (a*b)*b := by rw [mul_assoc,hb.2,mul_one]
      _ = c*b := by rw [hprod]
  exact ⟨hab,hac,hbc,by rw [hprod,hc.2]⟩

end E2.CompilerBlocks
