import E2.ProjectionRepair

namespace E2
noncomputable section
open scoped ComplexOrder
open Companion.Analytic

theorem selfadjoint_state_commutator {d : ℕ} (s : State d) (D : Mat d) (hD : D.IsHermitian) :
    hs (comm D s.xi)≤2*weighted s D := by
  have he : hs (s.xi*D)=hs (D*s.xi) := by
    change hsNorm (s.xi*D)=hsNorm (D*s.xi)
    rw [← hsNorm_conjTranspose (s.xi*D),Matrix.conjTranspose_mul,hD.eq,s.xi_positive.isHermitian.eq]
  calc
    _ ≤ hs (D*s.xi)+hs (s.xi*D) := hs_sub_le _ _
    _ = _ := by rw [he]; unfold weighted; ring

/-- The repaired projection retains a linear state-commutator estimate. -/
theorem projection_inclusion_repair_state {d : ℕ} (s : State d) (hd : 0<d)
    (F Q : Mat d) (hF : Domain.projection.Holds F) (hQ : Domain.projection.Holds Q)
    (η : ℝ) (hη : 0≤η) (hinc : weighted s ((1-F)*Q)≤η)
    (hFs : hs (comm F s.xi)≤η) (hQs : hs (comm Q s.xi)≤η) :
    ∃ R : Mat d, Domain.projection.Holds R ∧ F*R=R ∧
      weighted s (R-Q)≤6*η ∧ hs (comm R s.xi)≤13*η := by
  obtain ⟨R,hR,hFR,hclose⟩ := projection_inclusion_repair s hd F Q hF hQ η hη hinc hFs hQs
  refine ⟨R,hR,hFR,hclose,?_⟩
  have hD : (R-Q).IsHermitian := by
    simp only [Matrix.IsHermitian,Matrix.conjTranspose_sub,hR.1,hQ.1]
  have he : comm R s.xi=comm Q s.xi+comm (R-Q) s.xi := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [he]
  calc
    _ ≤ hs (comm Q s.xi)+hs (comm (R-Q) s.xi) := hsNorm_add_le _ _
    _ ≤ hs (comm Q s.xi)+2*weighted s (R-Q) :=
      add_le_add (le_refl _) (selfadjoint_state_commutator s _ hD)
    _ ≤ 13*η := by linarith

end
end E2
