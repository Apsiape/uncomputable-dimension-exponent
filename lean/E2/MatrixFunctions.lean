import E2.HSFunctionalCalculus
import E2.RawWords

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem finite_spectrum_continuous {d : ℕ} (A : Mat d) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

theorem matrix_function_mul {d : ℕ} (A : Mat d) (f g : ℝ → ℝ) :
    matrixFunction f A*matrixFunction g A=matrixFunction (fun x => f x*g x) A := by
  exact (cfc_mul f g A (finite_spectrum_continuous A f) (finite_spectrum_continuous A g)).symm

theorem matrix_function_sub {d : ℕ} (A : Mat d) (f g : ℝ → ℝ) :
    matrixFunction f A-matrixFunction g A=matrixFunction (fun x => f x-g x) A := by
  exact (cfc_sub f g A (finite_spectrum_continuous A f) (finite_spectrum_continuous A g)).symm

theorem matrix_function_id {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    matrixFunction id A=A := cfc_id ℝ A hA.isSelfAdjoint

theorem matrix_function_congr {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ x∈spectrum ℝ A,f x=g x) : matrixFunction f A=matrixFunction g A := by
  rw [matrix_function_spectral_form hA,matrix_function_spectral_form hA]
  have hd : Matrix.diagonal (fun i => (f (hA.eigenvalues i):ℂ)) =
      Matrix.diagonal (fun i => (g (hA.eigenvalues i):ℂ)) := by
    apply congrArg Matrix.diagonal
    funext i
    rw [hfg _ (hA.eigenvalues_mem_spectrum_real i)]
  rw [hd]

theorem matrix_function_hermitian {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (matrixFunction f A).IsHermitian := by
  rw [matrix_function_spectral_form hA]
  have hd : (Matrix.diagonal (fun i => (f (hA.eigenvalues i):ℂ))).conjTranspose =
      Matrix.diagonal (fun i => (f (hA.eigenvalues i):ℂ)) := by
    ext i j
    by_cases h : i=j
    · subst j
      simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply,h,Ne.symm h]
  simp only [Matrix.IsHermitian,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hd,Matrix.mul_assoc]

theorem matrix_function_positive {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i,0≤f (hA.eigenvalues i)) : (matrixFunction f A).PosSemidef := by
  rw [matrix_function_spectral_form hA]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact Complex.nonneg_iff.mpr ⟨hf i,by simp⟩

theorem projection_complement {d : ℕ} {F : Mat d} (hF : Domain.projection.Holds F) :
    Domain.projection.Holds (1-F) := by
  constructor
  · simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hF.1]
  · calc
      (1-F)*(1-F)=1-F-F+F*F := by noncomm_ring
      _ = 1-F := by rw [hF.2]; abel

theorem projection_positive {d : ℕ} {F : Mat d} (hF : Domain.projection.Holds F) : F.PosSemidef := by
  simpa only [hF.1,hF.2] using Matrix.posSemidef_conjTranspose_mul_self F

theorem projection_norm_le {d : ℕ} {F : Mat d} (hF : Domain.projection.Holds F) : ‖F‖ ≤ 1 := by
  have he : ‖F‖*‖F‖=‖F‖ := by
    rw [← CStarRing.norm_star_mul_self (x:=F),Matrix.star_eq_conjTranspose,hF.1,hF.2]
  nlinarith [norm_nonneg F]

theorem hs_square_gram {d n : ℕ} (E : Mat d) (X : Matrix (Fin d) (Fin n) ℂ) :
    hs (E*X)^2=(Matrix.trace (X.conjTranspose*(E.conjTranspose*E)*X)).re := by
  simp only [hs,hsNorm_sq,hsSquared_trace,Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- A positive Gram-matrix difference controls every weighted HS norm. -/
theorem hs_gram_mono {d n : ℕ} (E L : Mat d) (X : Matrix (Fin d) (Fin n) ℂ)
    (h : (L.conjTranspose*L-E.conjTranspose*E).PosSemidef) : hs (E*X) ≤ hs (L*X) := by
  apply (sq_le_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  rw [hs_square_gram,hs_square_gram]
  have ht := (Complex.nonneg_iff.mp (h.conjTranspose_mul_mul_same X).trace_nonneg).1
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re,sub_nonneg] using ht

theorem hs_neg_matrix {d n : ℕ} (E : Matrix (Fin d) (Fin n) ℂ) : hs (-E)=hs E := by
  simp only [hs,hsNorm,hsSquared,Matrix.neg_apply,Complex.normSq_neg]

theorem weighted_adjoint {d : ℕ} (s : State d) (E : Mat d) :
    weighted s E.conjTranspose ≤ weighted s E+hs (comm E s.xi) := by
  have he : s.xi*E=E*s.xi-comm E s.xi := by
    simp only [comm,Companion.Analytic.comm]
    abel
  unfold weighted
  change hsNorm (E.conjTranspose*s.xi) ≤ _
  rw [← hsNorm_conjTranspose (E.conjTranspose*s.xi),Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,s.xi_positive.isHermitian.eq,he]
  exact hs_sub_le _ _

end
end E2
