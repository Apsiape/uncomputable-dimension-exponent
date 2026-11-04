import E2.ProjectionRepair
import E2.FiniteMatrixTools

/-! Same-space orthogonality repair for the upper compiler. The existing
weighted inclusion repair gives a dimension-independent constant, sufficient
for the required quadratic flat-model loss. -/
namespace E2.CompilerOrthogonality
noncomputable section
open scoped Matrix.Norms.L2Operator
open Companion.Analytic E2.FiniteConstruction

theorem flat_orthogonality_repair {d : ℕ} (hd : 0 < d) (E F : Mat d)
    (hE : Domain.projection.Holds E) (hF : Domain.projection.Holds F)
    (η : ℝ) (hη : 0 ≤ η) (hEF : weighted (flatState d hd) (E*F) ≤ η) :
    ∃ R : Mat d, Domain.projection.Holds R ∧ E*R=0 ∧ R*E=0 ∧
      weighted (flatState d hd) (R-F) ≤ 6*η ∧
      weighted (flatState d hd) (R-F)^2 ≤ 36*η^2 := by
  let s := flatState d hd
  have hinc : weighted s ((1-(1-E))*F) ≤ η := by
    simpa only [sub_sub_cancel] using hEF
  have hEs : hs (comm (1-E) s.xi) ≤ η := by
    rw [flatState_commutes]
    simpa [hs, hsNorm, hsSquared] using hη
  have hFs : hs (comm F s.xi) ≤ η := by
    rw [flatState_commutes]
    simpa [hs, hsNorm, hsSquared] using hη
  obtain ⟨R,hR,hincR,hclose⟩ := projection_inclusion_repair s hd (1-E) F
    (projection_complement hE) hF η hη hinc hEs hFs
  have hER : E*R=0 := by
    have h : R-E*R=R := by simpa [Matrix.sub_mul] using hincR
    exact sub_eq_self.mp h
  have hRE : R*E=0 := by
    have h := congrArg Matrix.conjTranspose hER
    simpa only [Matrix.conjTranspose_mul,hE.1,hR.1,Matrix.conjTranspose_zero] using h
  refine ⟨R,hR,hER,hRE,hclose,?_⟩
  have hsq := pow_le_pow_left₀ (hsNorm_nonneg _) hclose 2
  change weighted (flatState d hd) (R-F)^2 ≤ (6*η)^2 at hsq
  simpa only [mul_pow, show (6:ℝ)^2=36 by norm_num] using hsq

/-- The three legal outcomes of the two-variable orthogonality context. -/
theorem orthogonality_pvm {d : ℕ} (E R : Mat d)
    (hE : Domain.projection.Holds E) (hR : Domain.projection.Holds R)
    (hER : E*R=0) (hRE : R*E=0) :
    Domain.projection.Holds (1-E-R) ∧ E+R+(1-E-R)=1 ∧
      E*(1-E-R)=0 ∧ R*(1-E-R)=0 ∧ (1-E-R)*E=0 ∧ (1-E-R)*R=0 := by
  have hrest : Domain.projection.Holds (1-E-R) := by
    constructor
    · simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hE.1,hR.1]
    · calc
        _ = 1-E-E-R-R+E*E+E*R+R*E+R*R := by noncomm_ring
        _ = 1-E-R := by rw [hE.2,hR.2,hER,hRE]; abel
  refine ⟨hrest,by abel,?_,?_,?_,?_⟩ <;>
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,hE.2,hR.2,hER,hRE,
      sub_self,sub_zero,zero_sub,neg_zero]

end
end E2.CompilerOrthogonality
