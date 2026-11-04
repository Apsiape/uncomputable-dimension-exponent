import E2.ClockData
import E2.Weighted
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem diagonal_intertwiner_bound {d a : ℕ} (x : Fin d → ℝ) (y : Fin a → ℝ)
    (Z : Matrix (Fin d) (Fin a) ℂ) (g : ℝ → ℝ) (L : NNReal)
    (h : ∀ i j,|g (x i)-g (y j)| ≤ (L:ℝ)*|x i-y j|) :
    hs (Matrix.diagonal (fun i => (g (x i):ℂ))*Z-Z*Matrix.diagonal (fun j => (g (y j):ℂ))) ≤
      L*hs (Matrix.diagonal (fun i => (x i:ℂ))*Z-Z*Matrix.diagonal (fun j => (y j:ℂ))) := by
  let D := Matrix.diagonal (fun i => (g (x i):ℂ))*Z-Z*Matrix.diagonal (fun j => (g (y j):ℂ))
  let E := Matrix.diagonal (fun i => (x i:ℂ))*Z-Z*Matrix.diagonal (fun j => (y j:ℂ))
  have hd (i : Fin d) (j : Fin a) : D i j=((g (x i)-g (y j):ℝ):ℂ)*Z i j := by
    simp only [D,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Complex.ofReal_sub]
    ring
  have he (i : Fin d) (j : Fin a) : E i j=((x i-y j:ℝ):ℂ)*Z i j := by
    simp only [E,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Complex.ofReal_sub]
    ring
  have hij (i : Fin d) (j : Fin a) : ‖D i j‖ ≤ (L:ℝ)*‖E i j‖ := by
    rw [hd,he]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h i j) (norm_nonneg (Z i j))
  have hsq : hs D^2 ≤ ((L:ℝ)*hs E)^2 := by
    simp only [hs,hsNorm_sq,hsSquared,Complex.normSq_eq_norm_sq,mul_pow]
    calc
      _ ≤ ∑ i,∑ j,((L:ℝ)*‖E i j‖)^2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hij i j) 2))
      _ = _ := by simp only [mul_pow,Finset.mul_sum]
  exact (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg L.coe_nonneg (hsNorm_nonneg _))).mp hsq

theorem hs_biunitary {d a : ℕ} (U : Mat d) (V : Mat a)
    (hU : Domain.unitary.Holds U) (hV : Domain.unitary.Holds V)
    (Z : Matrix (Fin d) (Fin a) ℂ) : hs (U.conjTranspose*Z*V)=hs Z := by
  change hsNorm (U.conjTranspose*Z*V)=hsNorm Z
  rw [Matrix.mul_assoc,hsNorm_unitary_left U.conjTranspose (Z*V)
    (by simpa using hU.2),hsNorm_unitary_right V Z hV.2]

theorem biunitary_intertwiner {d a : ℕ} (U D : Mat d) (V E : Mat a)
    (hU : U.conjTranspose*U=1) (hV : V.conjTranspose*V=1)
    (Z : Matrix (Fin d) (Fin a) ℂ) :
    U.conjTranspose*((U*D*U.conjTranspose)*Z-Z*(V*E*V.conjTranspose))*V =
      D*(U.conjTranspose*Z*V)-(U.conjTranspose*Z*V)*E := by
  calc
    _ = (U.conjTranspose*U)*D*(U.conjTranspose*Z*V) -
        (U.conjTranspose*Z*V)*E*(V.conjTranspose*V) := by
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
    _ = _ := by rw [hU,hV]; simp only [Matrix.one_mul,Matrix.mul_one]

theorem eigenvector_unitary {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    Domain.unitary.Holds (hA.eigenvectorUnitary : Mat d) := by
  constructor
  · simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self hA.eigenvectorUnitary

theorem matrix_function_spectral_form {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    matrixFunction g A = (hA.eigenvectorUnitary:Mat d)*
      Matrix.diagonal (fun i => (g (hA.eigenvalues i):ℂ))*(hA.eigenvectorUnitary:Mat d).conjTranspose := by
  rw [matrixFunction,hA.cfc_eq]
  rfl

theorem matrix_spectral_form {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary:Mat d)*
      Matrix.diagonal (fun i => (hA.eigenvalues i:ℂ))*(hA.eigenvectorUnitary:Mat d).conjTranspose := by
  exact hA.spectral_theorem

/-- The rectangular Hilbert-Schmidt bound follows by diagonalizing independently
on the left and right, then summing scalar squared Lipschitz inequalities. -/
theorem hs_spectral_lipschitz {d a : ℕ} (A : Mat d) (B : Mat a)
    (Z : Matrix (Fin d) (Fin a) ℂ) (g : ℝ → ℝ) (L : NNReal)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hg : LipschitzOnWith L g (spectrum ℝ A ∪ spectrum ℝ B)) :
    hs (matrixFunction g A*Z-Z*matrixFunction g B) ≤ L*hs (A*Z-Z*B) := by
  let U : Mat d := hA.eigenvectorUnitary
  let V : Mat a := hB.eigenvectorUnitary
  let W := U.conjTranspose*Z*V
  have hU := eigenvector_unitary hA
  have hV := eigenvector_unitary hB
  have hscalar (i : Fin d) (j : Fin a) :
      |g (hA.eigenvalues i)-g (hB.eigenvalues j)| ≤ (L:ℝ)*|hA.eigenvalues i-hB.eigenvalues j| := by
    simpa only [Real.dist_eq] using hg.dist_le_mul _
      (Set.mem_union_left _ (hA.eigenvalues_mem_spectrum_real i)) _
      (Set.mem_union_right _ (hB.eigenvalues_mem_spectrum_real j))
  calc
    _ = hs (U.conjTranspose*(matrixFunction g A*Z-Z*matrixFunction g B)*V) :=
      (hs_biunitary U V hU hV _).symm
    _ = hs (Matrix.diagonal (fun i => (g (hA.eigenvalues i):ℂ))*W-
        W*Matrix.diagonal (fun j => (g (hB.eigenvalues j):ℂ))) := by
      rw [matrix_function_spectral_form hA,matrix_function_spectral_form hB,
        biunitary_intertwiner U _ V _ hU.1 hV.1]
    _ ≤ (L:ℝ)*hs (Matrix.diagonal (fun i => (hA.eigenvalues i:ℂ))*W-
        W*Matrix.diagonal (fun j => (hB.eigenvalues j:ℂ))) :=
      diagonal_intertwiner_bound _ _ W g L hscalar
    _ = (L:ℝ)*hs (A*Z-Z*B) := by
      congr 1
      rw [← biunitary_intertwiner U _ V _ hU.1 hV.1 Z]
      rw [← matrix_spectral_form hA,← matrix_spectral_form hB]
      exact hs_biunitary U V hU hV _

end
end E2
