import E2.TernaryRepair
import E2.RawWords

namespace E2
noncomputable section
open Companion.Analytic
open scoped Matrix.Norms.L2Operator

theorem weighted_sub {d : ℕ} (s : State d) (A B : Mat d) :
    weighted s (A-B) ≤ weighted s A+weighted s B := by
  simpa only [weighted,Matrix.sub_mul] using hs_sub_le (A*s.xi) (B*s.xi)

theorem state_sub {d : ℕ} (s : State d) (A B : Mat d) :
    hs (comm (A-B) s.xi) ≤ hs (comm A s.xi)+hs (comm B s.xi) := by
  have he : comm (A-B) s.xi=comm A s.xi-comm B s.xi := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]; abel
  rw [he]; exact hs_sub_le _ _

theorem comm_sub_left_eq {d : ℕ} (A B X : Mat d) :
    comm (A-B) X=comm A X-comm B X := by
  simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]; abel
theorem comm_sub_right_eq {d : ℕ} (A B X : Mat d) :
    comm X (A-B)=comm X A-comm X B := by
  simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]; abel
theorem comm_one_left_eq {d : ℕ} (X : Mat d) : comm 1 X=0 := by
  simp [comm,Companion.Analytic.comm]
theorem comm_one_right_eq {d : ℕ} (X : Mat d) : comm X 1=0 := by
  simp [comm,Companion.Analytic.comm]
theorem weighted_zero_eq {d : ℕ} (s : State d) : weighted s (0:Mat d)=0 := by
  simp [weighted,hs,hsNorm,hsSquared]

/-- Two replacements have additive cost on the original state. -/
theorem joint_commutator_replacements {d : ℕ} (s : State d) (η : ℝ)
    (A B R S : Mat d) (hnA : ‖A‖ ≤ 1) (hnS : ‖S‖ ≤ 1)
    (hRA : ‖R-A‖ ≤ 2) (hSB : ‖S-B‖ ≤ 2)
    (hR : weighted s (R-A) ≤ 6*η) (hS : weighted s (S-B) ≤ 6*η)
    (hstateA : hs (comm A s.xi) ≤ η) (hstateS : hs (comm S s.xi) ≤ 13*η)
    (hcomm : weighted s (comm A B) ≤ η) : weighted s (comm R S) ≤ 53*η := by
  have he : comm R S=comm (R-A) S+comm A (S-B)+comm A B := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]; abel
  have hr := commutator_replace s (R-A) S hnS
  have hs' := commutator_replace s (S-B) A hnA
  rw [weighted_comm_symm] at hs'
  have h1 := mul_le_mul hRA hstateS (hsNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have h2 := mul_le_mul hSB hstateA (hsNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [he]
  exact (weighted_add s _ _).trans (by linarith [weighted_add s (comm (R-A) S) (comm A (S-B))])

theorem joint_later_replacement {d : ℕ} (s : State d) (η : ℝ) (U Q R : Mat d)
    (hnU : ‖U‖ ≤ 1) (hnD : ‖R-Q‖ ≤ 2) (hD : weighted s (R-Q) ≤ 6*η)
    (hU : hs (comm U s.xi) ≤ η) (hraw : weighted s (comm U Q) ≤ η) :
    weighted s (comm U R) ≤ 15*η := by
  have he : comm U R=comm U Q+comm U (R-Q) := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]; abel
  have h := commutator_replace s (R-Q) U hnU
  rw [weighted_comm_symm] at h
  have hm := mul_le_mul hnD hU (hsNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [he]
  exact (weighted_add s _ _).trans (by linarith)

/-- Replacing the data on both sides of a conjugated flip costs 15 eta. -/
theorem joint_own_replacement {d : ℕ} (s : State d) (η : ℝ) (U F Q R : Mat d)
    (hnU : ‖U‖ ≤ 1) (hnD : ‖R-Q‖ ≤ 2) (hD : weighted s (R-Q) ≤ 6*η)
    (hU : hs (comm U s.xi) ≤ η) (hraw : weighted s (U*Q*U-(F-Q)) ≤ η) :
    weighted s (U*R*U-(F-R)) ≤ 15*η := by
  have he : U*R*U-(F-R)=U*((R-Q)*U)+(U*Q*U-(F-Q))+(R-Q) := by noncomm_ring
  have hright := weighted_right s U (R-Q)
  have hleft := weighted_left s U ((R-Q)*U)
  have hm := mul_le_mul hnD hU (hsNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have ha := mul_le_mul_of_nonneg_right hnU (weighted_nonneg s (R-Q))
  have hb := mul_le_mul_of_nonneg_right hnU (weighted_nonneg s ((R-Q)*U))
  rw [he]
  exact (weighted_add s _ _).trans (by linarith [weighted_add s (U*((R-Q)*U)) (U*Q*U-(F-Q))])

end
end E2
