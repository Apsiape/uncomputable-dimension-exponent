import E2.CompilerUnitaryDiagonal
import E2.CompilerPositiveLift
import E2.CompilerFlatExtension

namespace E2.CompilerRealification
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open E2.CompilerBlocks E2.CompilerDomains E2.CompilerFrontend E2.FiniteConstruction
variable {d : ℕ}

/-- Exact multiplication of unitary matrices. -/
theorem unitary_mul (U V : Mat d) (hU : Domain.unitary.Holds U)
    (hV : Domain.unitary.Holds V) : Domain.unitary.Holds (U*V) := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    change (star V * star U) * (U*V) = 1
    calc
      _ = star V * (star U * U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [show star U*U=1 from hU.1,mul_one]; exact hV.1
  · rw [Matrix.conjTranspose_mul]
    change (U*V)*(star V*star U) = 1
    calc
      _ = U*(V*star V)*star U := by simp only [mul_assoc]
      _ = 1 := by rw [show V*star V=1 from hV.2,mul_one]; exact hU.2

/-- Unitary conjugation preserves reflection domains. -/
theorem conjugate_reflection (V R : Mat d) (hV : Domain.unitary.Holds V)
    (hR : Domain.reflection.Holds R) : Domain.reflection.Holds (V*R*star V) := by
  constructor
  · change star (V*R*star V)=V*R*star V
    simp only [star_mul,star_star,show star R=R from hR.1,mul_assoc]
  · calc
      _ = V*R*(star V*V)*R*star V := by simp only [mul_assoc]
      _ = V*(R*R)*star V := by rw [show star V*V=1 from hV.1,mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [hR.2,mul_one]; exact hV.2

def realFlip (d : ℕ) : Mat (2*d) := doubleMatrix (diag (1:Mat d) (-1))

theorem realFlip_reflection : Domain.reflection.Holds (realFlip d) := by
  apply doubleMatrix_reflection
  exact reflection_diag reflection_one ⟨by simp,by simp⟩

/-- Conjugating a diagonal complex unitary by the real/imaginary flip
implements its adjoint on the realified space. -/
theorem flip_diagonal (z : Fin d → ℂ) :
    realFlip d * realify (Matrix.diagonal z) * realFlip d =
      star (realify (Matrix.diagonal z)) := by
  have he : diag (1:Mat d) (-1) * block (Matrix.diagonal z) * diag 1 (-1) =
      star (block (Matrix.diagonal z)) := by
    ext i j a b
    fin_cases i <;> fin_cases j <;> by_cases hab : a=b <;>
      simp_all [diag,block,realPart,imagPart,Matrix.mul_apply,Fin.sum_univ_two,
        eq_comm]
  rw [realFlip,realify,← doubleMatrix_mul,← doubleMatrix_mul,he,doubleMatrix_star]

/-- Each original unitary has two exact reflection factors in the common
realification space. Both the dimension and the embedding are independent of U. -/
theorem realified_unitary_factors (U : Mat d) (hU : Domain.unitary.Holds U) :
    ∃ A B : Mat (2*d), Domain.reflection.Holds A ∧ Domain.reflection.Holds B ∧
      A*B=realify U := by
  obtain ⟨V,z,hV,he⟩ := unitary_diagonal U hU
  let D := Matrix.diagonal z
  have hD : Domain.unitary.Holds D := by
    have hVs : Domain.unitary.Holds (star V) := by simpa [Domain.Holds,Matrix.star_eq_conjTranspose] using And.intro hV.2 hV.1
    have hc := unitary_mul (star V*U) V (unitary_mul (star V) U hVs hU) hV
    have hid : star V*U*V=D := by
      rw [he]
      change star V*(V*D*star V)*V=D
      calc
        _ = (star V*V)*D*(star V*V) := by simp only [mul_assoc]
        _ = D := by rw [show star V*V=1 from hV.1,one_mul,mul_one]
    rwa [hid] at hc
  let W := realify V
  let T := realify D
  let J := realFlip d
  have hW : Domain.unitary.Holds W := realify_domain _ V hV
  have hT : Domain.unitary.Holds T := realify_domain _ D hD
  have hJ : Domain.reflection.Holds J := realFlip_reflection
  have hJTJ : J*T*J=star T := flip_diagonal z
  have hJT : Domain.reflection.Holds (J*T) := by
    have hmove : star T*J=J*T := by
      rw [← hJTJ,mul_assoc,hJ.2,mul_one]
    constructor
    · rw [Matrix.conjTranspose_mul]
      change star T*star J=J*T
      rw [show star J=J from hJ.1,hmove]
    · rw [← mul_assoc,hJTJ]
      exact hT.1
  refine ⟨W*J*star W,W*(J*T)*star W,conjugate_reflection W J hW hJ,
    conjugate_reflection W (J*T) hW hJT,?_⟩
  calc
    _ = W*(J*J)*T*star W := by
      calc
        _ = W*J*(star W*W)*J*T*star W := by simp only [mul_assoc]
        _ = W*(J*J)*T*star W := by rw [show star W*W=1 from hW.1,mul_one]; simp only [mul_assoc]
    _ = W*T*star W := by rw [hJ.2,mul_one]
    _ = realify U := by
      rw [he]
      change realify V*realify D*star (realify V) = realify (V*D*star V)
      simp only [realify_mul,realify_star]

end
end E2.CompilerRealification
