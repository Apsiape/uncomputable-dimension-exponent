import E2.CompilerOrthogonality
import E2.CompilerCertificates
import QIT.Util.Matrix.PosSqrt

namespace E2.CompilerFlat
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Companion.Analytic E2.FiniteConstruction

/-- The supplied positive square root is uniquely determined by the density
matrix. Flatness therefore fixes the original state's square root as well. -/
theorem xi_eq_of_rho {d : ℕ} (s t : State d) (hρ : s.rho=t.rho) : s.xi=t.xi := by
  have hs : CFC.sqrt s.rho=s.xi := CFC.sqrt_unique s.xi_square s.xi_positive.nonneg
  have ht : CFC.sqrt t.rho=t.xi := CFC.sqrt_unique t.xi_square t.xi_positive.nonneg
  exact hs.symm.trans ((congrArg CFC.sqrt hρ).trans ht)

theorem state_eq_of_rho {d : ℕ} (s t : State d) (hρ : s.rho=t.rho) : s=t := by
  have hxi := xi_eq_of_rho s t hρ
  cases s
  cases t
  cases hρ
  cases hxi
  rfl

theorem flat_model_state {ι : Type*} {P : Presentation ι} {d : ℕ} {δ : ℝ}
    (m : Model P d δ) (hm : m.Flat) : m.state=flatState d m.positive_dimension := by
  apply state_eq_of_rho
  simpa only [Model.Flat,flatState,one_div] using hm

theorem flat_state_weighted_square {d : ℕ} (hd : 0<d) (M : Mat d) :
    weighted (flatState d hd) M ^ 2 = hs M ^ 2 / (d : ℝ) := by
  simp only [weighted,flatState,Matrix.mul_smul,Matrix.mul_one,CompilerCertificates.hs_smul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (d:ℝ)))]
  rw [mul_pow,inv_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ d)]
  ring

/-- Orthogonality repair for the original flat model state, not a replacement
state or a full-rank hypothesis. The repaired projection stays in dimension d. -/
theorem flat_model_orthogonality_repair {ι : Type*} {P : Presentation ι} {d : ℕ} {δ : ℝ}
    (m : Model P d δ) (hm : m.Flat) (E F : Mat d)
    (hE : Domain.projection.Holds E) (hF : Domain.projection.Holds F)
    (η : ℝ) (hη : 0≤η) (hEF : weighted m.state (E*F)≤η) :
    ∃ R : Mat d, Domain.projection.Holds R ∧ E*R=0 ∧ R*E=0 ∧
      weighted m.state (R-F)≤6*η ∧ weighted m.state (R-F)^2≤36*η^2 := by
  rw [flat_model_state m hm] at hEF ⊢
  exact CompilerOrthogonality.flat_orthogonality_repair m.positive_dimension E F hE hF η hη hEF

end
end E2.CompilerFlat
