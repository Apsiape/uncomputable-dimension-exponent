import E2.ProjectionState
import E2.MeasurementDefs

namespace E2
noncomputable section

/-- The inactive/active-zero/active-one measurement after exact inclusion repair. -/
def conditionalMeasurement {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) : Measurement d := by
  have hRF : R*F=R := by
    have h := congrArg Matrix.conjTranspose hFR
    simpa only [Matrix.conjTranspose_mul,hF.1,hR.1] using h
  refine {
    outcomes := 3
    arity := Or.inr rfl
    projection := fun a => if a.val=0 then 1-F else if a.val=1 then F-R else R
    selfadjoint := ?_
    idempotent := ?_
    orthogonal := ?_
    complete := ?_ }
  · intro a
    fin_cases a
    · exact (projection_complement hF).1
    · change (F-R).conjTranspose=F-R
      simp only [Matrix.conjTranspose_sub,hF.1,hR.1]
    · exact hR.1
  · intro a
    fin_cases a
    · exact (projection_complement hF).2
    · change (F-R)*(F-R)=F-R
      simp only [Matrix.mul_sub,Matrix.sub_mul,hF.2,hR.2,hFR,hRF]
      abel
    · exact hR.2
  · intro a b hab
    fin_cases a <;> fin_cases b
    all_goals dsimp at *
    all_goals first | exact False.elim (hab rfl) | (simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_one,hF.2,hR.2,hFR,hRF]; abel)
  · simp [Fin.sum_univ_succ]

theorem conditional_pvm_exact {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) :
    ∃ m : Measurement d, m.outcomes=3 ∧ ∀ j : Fin 3,
      m.projection (m.index j.val)=![1-F,F-R,R] j := by
  refine ⟨conditionalMeasurement F R hF hR hFR,rfl,?_⟩
  intro j
  fin_cases j <;> rfl

end
end E2
