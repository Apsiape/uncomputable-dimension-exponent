import E2.CantorDistance

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open scoped Matrix.Norms.Frobenius in
theorem hs_matrix_eq_zero {d : ℕ} (A : Mat d) : hs A=0 ↔ A=0 := by
  change hsNorm A=0 ↔ A=0
  rw [hsNorm_eq_frobenius,norm_eq_zero]

theorem hs_matrix_zero {d : ℕ} : hs (0:Mat d)=0 := (hs_matrix_eq_zero _).mpr rfl

/-- Zero-error rectangular functional calculus supplies exact intertwining. -/
theorem matrix_function_intertwines {d : ℕ} (A B Z : Mat d)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hZ : A*Z=Z*B)
    (f : ℝ → ℝ) (L : NNReal) (hf : LipschitzWith L f) :
    matrixFunction f A*Z=Z*matrixFunction f B := by
  have h := hs_functional_calculus A B Z f L hA hB hf.lipschitzOnWith
  rw [hZ,sub_self,hs_matrix_zero,mul_zero] at h
  exact sub_eq_zero.mp ((hs_matrix_eq_zero _).mp (le_antisymm h (hsNorm_nonneg _)))

theorem positive_contraction_spectrum {d : ℕ} [NeZero d] (A : Mat d)
    (hA : Domain.positiveContraction.Holds A) (x : ℝ) (hx : x∈spectrum ℝ A) : 0≤x ∧ x≤1 := by
  exact ⟨spectrum_nonneg_of_nonneg hA.1.nonneg hx,
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans (positive_contraction_norm hA))⟩

theorem matrix_function_branch {d : ℕ} (D : Mat d) (hD : D.IsHermitian) (b : Bool) :
    matrixFunction (cantorBranch b) D=
      ((if b then 3/4 else 0):ℂ) • (1:Mat d)+(1/4:ℂ) • D := by
  have he : cantorBranch b=(fun x : ℝ => (if b then 3/4 else 0)+(1/4)*id x) := by
    funext x
    simp only [cantorBranch,id_eq]
    ring
  rw [he,←matrix_function_add,matrix_function_const hD,
    ←matrix_function_real_smul,matrix_function_id hD]
  cases b <;> simp

def blockAffine {d : ℕ} (D P : Mat d) : Mat d := (1/4:ℂ) • D+(3/4:ℂ) • P

theorem blockAffine_hermitian {d : ℕ} (D P : Mat d) (hD : D.IsHermitian)
    (hP : Domain.projection.Holds P) : (blockAffine D P).IsHermitian := by
  change (blockAffine D P).conjTranspose=blockAffine D P
  simp [blockAffine,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,hD.eq,hP.1]

theorem blockAffine_intertwines {d : ℕ} (D P : Mat d) (hD : D.IsHermitian)
    (hP : Domain.projection.Holds P) (hDP : D*P=P*D) :
    blockAffine D P*P=P*matrixFunction (cantorBranch true) D ∧
    blockAffine D P*(1-P)=(1-P)*matrixFunction (cantorBranch false) D := by
  rw [matrix_function_branch D hD true,matrix_function_branch D hD false]
  simp only [Bool.false_eq_true,↓reduceIte,zero_smul,zero_add]
  constructor
  · simp only [blockAffine,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.mul_one,hP.2,hDP]
    abel
  · simp only [blockAffine,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,hP.2,hDP,sub_self,smul_zero,add_zero]
    module

theorem blockAffine_function {d : ℕ} (D P : Mat d) (hD : D.IsHermitian)
    (hP : Domain.projection.Holds P) (hDP : D*P=P*D)
    (f : ℝ → ℝ) (L : NNReal) (hf : LipschitzWith L f) :
    matrixFunction f (blockAffine D P)=
      P*matrixFunction f (matrixFunction (cantorBranch true) D)+
      (1-P)*matrixFunction f (matrixFunction (cantorBranch false) D) := by
  have h := blockAffine_intertwines D P hD hP hDP
  have h1 := matrix_function_intertwines (blockAffine D P) _ P (blockAffine_hermitian D P hD hP)
    (matrix_function_hermitian hD _) h.1 f L hf
  have h0 := matrix_function_intertwines (blockAffine D P) _ (1-P) (blockAffine_hermitian D P hD hP)
    (matrix_function_hermitian hD _) h.2 f L hf
  calc
    _=matrixFunction f (blockAffine D P)*P+matrixFunction f (blockAffine D P)*(1-P) := by noncomm_ring
    _=_ := by rw [h1,h0]

theorem blockAffine_distance {d : ℕ} [NeZero d] (D P : Mat d)
    (hD : Domain.positiveContraction.Holds D) (hP : Domain.projection.Holds P) (hDP : D*P=P*D) :
    matrixFunction (fun x => Metric.infDist x cantorSet) (blockAffine D P)=
      (1/4:ℂ) • matrixFunction (fun x => Metric.infDist x cantorSet) D := by
  have hDh := hD.1.isHermitian
  have hb (b : Bool) : matrixFunction (fun x => Metric.infDist x cantorSet)
      (matrixFunction (cantorBranch b) D)=
      (1/4:ℂ) • matrixFunction (fun x => Metric.infDist x cantorSet) D := by
    rw [matrix_function_comp hDh]
    calc
      _=matrixFunction (fun x => (1/4:ℝ)*Metric.infDist x cantorSet) D := by
        apply matrix_function_congr hDh
        intro x hx
        rw [cantor_distance_branch b x (positive_contraction_spectrum D hD x hx)]
        ring
      _=_ := by simpa using (matrix_function_real_smul D (1/4) (fun x => Metric.infDist x cantorSet)).symm
  rw [blockAffine_function D P hDh hP hDP _ 1 cantor_distance_lipschitz,hb,hb]
  simp only [Matrix.sub_mul,Matrix.one_mul]
  abel

theorem blockAffine_digit {d : ℕ} [NeZero d] (D P : Mat d)
    (hD : Domain.positiveContraction.Holds D) (hP : Domain.projection.Holds P) (hDP : D*P=P*D) :
    matrixFunction digitFunction (blockAffine D P)=P := by
  have hDh := hD.1.isHermitian
  have hb (b : Bool) : matrixFunction digitFunction (matrixFunction (cantorBranch b) D)=
      ((if b then 1 else 0):ℂ) • (1:Mat d) := by
    rw [matrix_function_comp hDh]
    calc
      _=matrixFunction (fun _ => if b then (1:ℝ) else 0) D := by
        apply matrix_function_congr hDh
        intro x hx
        exact digitFunction_branch b x (positive_contraction_spectrum D hD x hx)
      _=_ := by
        have hc := matrix_function_const hDh (if b then (1:ℝ) else 0)
        cases b <;> simpa using hc
  rw [blockAffine_function D P hDh hP hDP _ 2 digitFunction_lipschitz,hb,hb]
  simp

end
end E2

#print axioms E2.hs_matrix_eq_zero
#print axioms E2.hs_matrix_zero
#print axioms E2.matrix_function_intertwines
#print axioms E2.positive_contraction_spectrum
#print axioms E2.matrix_function_branch
#print axioms E2.blockAffine
#print axioms E2.blockAffine_hermitian
#print axioms E2.blockAffine_intertwines
#print axioms E2.blockAffine_function
#print axioms E2.blockAffine_distance
#print axioms E2.blockAffine_digit
