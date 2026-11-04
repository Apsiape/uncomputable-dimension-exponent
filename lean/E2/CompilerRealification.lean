import E2.CompilerFlatten
import QIT.Util.Matrix.PosSqrt

namespace E2.CompilerRealification
noncomputable section
open E2.CompilerBlocks
open scoped BigOperators ComplexOrder MatrixOrder
variable {d : ℕ}

def realPart (M : Mat d) : Mat d := fun i j => (M i j).re
def imagPart (M : Mat d) : Mat d := fun i j => (M i j).im

theorem realPart_mul (M N : Mat d) :
    realPart (M*N)=realPart M*realPart N-imagPart M*imagPart N := by
  ext i j
  simp [realPart,imagPart,Matrix.mul_apply,Complex.mul_re,Finset.sum_sub_distrib]

theorem imagPart_mul (M N : Mat d) :
    imagPart (M*N)=realPart M*imagPart N+imagPart M*realPart N := by
  ext i j
  simp [realPart,imagPart,Matrix.mul_apply,Complex.mul_im,Finset.sum_add_distrib]

def block (M : Mat d) : Block (Mat d) := !![realPart M,-imagPart M;imagPart M,realPart M]

@[simp] theorem block_add (M N : Mat d) : block (M+N)=block M+block N := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> simp [block,realPart,imagPart] <;> abel

@[simp] theorem block_one : block (1 : Mat d)=1 := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> by_cases h : a=b <;>
    simp [block,realPart,imagPart,Matrix.one_apply,h]

@[simp] theorem block_mul (M N : Mat d) : block (M*N)=block M*block N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block,Matrix.mul_apply,Fin.sum_univ_two,realPart_mul,imagPart_mul] <;> abel

@[simp] theorem block_star (M : Mat d) : block (star M)=star (block M) := by
  ext i j a b
  fin_cases i <;> fin_cases j <;>
    simp [block,realPart,imagPart,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]

@[simp] theorem block_neg (M : Mat d) : block (-M) = -block M := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> simp [block,realPart,imagPart] <;> abel

@[simp] theorem block_zero : block (0 : Mat d)=0 := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> simp [block,realPart,imagPart] <;> abel

@[simp] theorem block_rat_smul (q : ℚ) (M : Mat d) : block ((q:ℂ) • M)=(q:ℂ) • block M := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> simp [block,realPart,imagPart,Complex.mul_re,Complex.mul_im]

@[simp] theorem flatten_neg (M : Block (Mat d)) : flatten (-M) = -flatten M := rfl
@[simp] theorem flatten_smul (c : ℂ) (M : Block (Mat d)) : flatten (c • M)=c • flatten M := rfl

def realify (M : Mat d) : Mat (2*d) := doubleMatrix (block M)

@[simp] theorem realify_one : realify (1 : Mat d)=1 := by simp [realify]
@[simp] theorem realify_mul (M N : Mat d) : realify (M*N)=realify M*realify N := by simp [realify]
@[simp] theorem realify_star (M : Mat d) : realify (star M)=star (realify M) := by simp [realify]
@[simp] theorem realify_add (M N : Mat d) : realify (M+N)=realify M+realify N := by
  simp [realify,doubleMatrix,flatten_add]
@[simp] theorem realify_neg (M : Mat d) : realify (-M) = -realify M := by
  simp [realify,doubleMatrix,flatten]
@[simp] theorem realify_zero : realify (0 : Mat d)=0 := by simp [realify,doubleMatrix]
@[simp] theorem realify_sub (M N : Mat d) : realify (M-N)=realify M-realify N := by
  simp only [sub_eq_add_neg,realify_add,realify_neg]

@[simp] theorem realify_rat_smul (q : ℚ) (M : Mat d) :
    realify ((q:ℂ) • M)=(q:ℂ) • realify M := by
  simp [realify,doubleMatrix,flatten,block_rat_smul]

/-- Real-coefficient equations, including guards, survive realification exactly. -/
theorem eval_realify {ι : Type*} (x : ι → Mat d) (p : Poly ι) :
    Poly.eval (fun i => realify (x i)) p=realify (Poly.eval x p) := by
  induction p with
  | const q => simpa only [Poly.eval,realify_rat_smul,realify_one]
  | var i => rfl
  | add p q hp hq => simpa only [Poly.eval,realify_add] using congrArg₂ (·+·) hp hq
  | mul p q hp hq => simpa only [Poly.eval,realify_mul] using congrArg₂ (·*·) hp hq
  | adj p hp => simpa only [Poly.eval,← Matrix.star_eq_conjTranspose,realify_star] using congrArg star hp

theorem realify_positive (M : Mat d) (hM : M.PosSemidef) : (realify M).PosSemidef := by
  let S := QIT.psdSqrt M
  have hS : S.conjTranspose*S=M := by
    rw [(QIT.psdSqrt_isHermitian M).eq]
    exact QIT.psdSqrt_mul_self_of_posSemidef hM
  rw [← hS,realify_mul]
  change (realify (star S)*realify S).PosSemidef
  rw [realify_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem realify_domain (D : Domain) (M : Mat d) (hM : D.Holds M) :
    D.Holds (realify M) := by
  cases D with
  | positiveContraction =>
    exact ⟨realify_positive M hM.1,by simpa using realify_positive (1-M) hM.2⟩
  | projection =>
    refine ⟨?_,?_⟩
    · change star (realify M)=realify M
      rw [← realify_star]
      exact congrArg realify hM.1
    · rw [← realify_mul,hM.2]
  | reflection =>
    refine ⟨?_,?_⟩
    · change star (realify M)=realify M
      rw [← realify_star]
      exact congrArg realify hM.1
    · rw [← realify_mul,hM.2,realify_one]
  | unitary =>
    constructor
    · change star (realify M)*realify M=1
      rw [← realify_star,← realify_mul]
      change realify (M.conjTranspose*M)=1
      rw [hM.1,realify_one]
    · change realify M*star (realify M)=1
      rw [← realify_star,← realify_mul]
      change realify (M*M.conjTranspose)=1
      rw [hM.2,realify_one]

end
end E2.CompilerRealification
