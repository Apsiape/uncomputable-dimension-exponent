import E2.CompilerRealification
import E2.MatrixFunctions
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

namespace E2.CompilerRealification
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- All scalar functions are continuous on the finite complex matrix spectrum. -/
theorem finite_complex_continuous {d : ℕ} (M : Mat d) (f : ℂ → ℂ) :
    ContinuousOn f (spectrum ℂ M) := M.finite_spectrum.continuousOn f

/-- Diagonalize a unitary through its selfadjoint argument. Finiteness makes
argument continuous even at the principal branch cut. -/
theorem unitary_diagonal {d : ℕ} (U : Mat d) (hU : Domain.unitary.Holds U) :
    ∃ V : Mat d, ∃ z : Fin d → ℂ, Domain.unitary.Holds V ∧
      U = V * Matrix.diagonal z * V.conjTranspose := by
  have hu : U ∈ unitary (Mat d) := hU
  have : IsStarNormal U := isStarNormal_of_mem_unitary hu
  let argC : ℂ → ℂ := fun z => z.arg
  let H := cfc argC U
  have hH : IsSelfAdjoint H := by
    change star (cfc argC U) = cfc argC U
    rw [← cfc_star]
    congr 1
    funext z
    simp [argC]
  have hcos : cfc Real.cos H = cfc (fun z : ℂ => (Real.cos z.arg : ℂ)) U := by
    rw [cfc_real_eq_complex Real.cos hH]
    change cfc (fun z : ℂ => (Real.cos z.re : ℂ)) (cfc argC U) = _
    rw [← cfc_comp' (hg := (U.finite_spectrum.image argC).continuousOn _)
      (hf := finite_complex_continuous U argC)]
    simp only [argC,Complex.ofReal_re]
  have hsin : cfc Real.sin H = cfc (fun z : ℂ => (Real.sin z.arg : ℂ)) U := by
    rw [cfc_real_eq_complex Real.sin hH]
    change cfc (fun z : ℂ => (Real.sin z.re : ℂ)) (cfc argC U) = _
    rw [← cfc_comp' (hg := (U.finite_spectrum.image argC).continuousOn _)
      (hf := finite_complex_continuous U argC)]
    simp only [argC,Complex.ofReal_re]
  have hrec : cfc Real.cos H + Complex.I • cfc Real.sin H = U := by
    rw [hcos,hsin,← cfc_const_mul (hf := finite_complex_continuous U _),
      ← cfc_add (hf := finite_complex_continuous U _) (hg := finite_complex_continuous U _)]
    conv_rhs => rw [← cfc_id' ℂ U]
    apply cfc_congr
    intro z hz
    have hn : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn
    simp only [Complex.cos_arg hz0,Complex.sin_arg,hn,div_one]
    simpa only [mul_comm Complex.I] using Complex.re_add_im z
  let V : Mat d := hH.isHermitian.eigenvectorUnitary
  refine ⟨V,fun i => (Real.cos (hH.isHermitian.eigenvalues i) : ℂ) +
    Complex.I * (Real.sin (hH.isHermitian.eigenvalues i) : ℂ),
    eigenvector_unitary hH.isHermitian,?_⟩
  rw [← hrec]
  change matrixFunction Real.cos H + Complex.I • matrixFunction Real.sin H = _
  rw [matrix_function_spectral_form hH.isHermitian,
    matrix_function_spectral_form hH.isHermitian]
  have hd : Matrix.diagonal (fun i => (Real.cos (hH.isHermitian.eigenvalues i) : ℂ) +
      Complex.I * (Real.sin (hH.isHermitian.eigenvalues i) : ℂ)) =
      Matrix.diagonal (fun i => (Real.cos (hH.isHermitian.eigenvalues i) : ℂ)) +
      Complex.I • Matrix.diagonal (fun i => (Real.sin (hH.isHermitian.eigenvalues i) : ℂ)) := by
    rw [← Matrix.diagonal_smul,← Matrix.diagonal_add]
    rfl
  rw [hd,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]

end
end E2.CompilerRealification
