import E2.JointReplacement

namespace E2
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator

def ternaryEffect {d : ℕ} (F Q : Mat d) (a : Fin 3) : Mat d := ![1-F,F-Q,Q] a

theorem weighted_comm_complement_left {d : ℕ} (s : State d) (A B : Mat d) :
    weighted s (comm (1-A) B)=weighted s (comm A B) := by
  rw [comm_sub_left_eq,comm_one_left_eq,zero_sub,weighted_neg]
theorem weighted_comm_complement_right {d : ℕ} (s : State d) (A B : Mat d) :
    weighted s (comm A (1-B))=weighted s (comm A B) := by
  rw [comm_sub_right_eq,comm_one_right_eq,zero_sub,weighted_neg]
theorem state_complement {d : ℕ} (s : State d) (A : Mat d) :
    hs (comm (1-A) s.xi)=hs (comm A s.xi) := by
  rw [comm_sub_left_eq,comm_one_left_eq,zero_sub,hs_neg_matrix]

theorem effect_comm_left {d : ℕ} (s : State d) (F Q X : Mat d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hF : weighted s (comm F X) ≤ κ) (hQ : weighted s (comm Q X) ≤ κ) (a : Fin 3) :
    weighted s (comm (ternaryEffect F Q a) X) ≤ 2*κ := by
  fin_cases a
  · change weighted s (comm (1-F) X) ≤ _
    rw [weighted_comm_complement_left]; linarith
  · change weighted s (comm (F-Q) X) ≤ _
    rw [comm_sub_left_eq]; exact (weighted_sub s _ _).trans (by linarith)
  · exact hQ.trans (by linarith)

theorem effect_comm_right {d : ℕ} (s : State d) (F Q X : Mat d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hF : weighted s (comm X F) ≤ κ) (hQ : weighted s (comm X Q) ≤ κ) (a : Fin 3) :
    weighted s (comm X (ternaryEffect F Q a)) ≤ 2*κ := by
  rw [weighted_comm_symm]
  apply effect_comm_left s F Q X κ hκ
  · simpa only [weighted_comm_symm] using hF
  · simpa only [weighted_comm_symm] using hQ

theorem effect_comm_pair {d : ℕ} (s : State d) (F Q G R : Mat d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hFG : weighted s (comm F G) ≤ κ) (hFR : weighted s (comm F R) ≤ κ)
    (hQG : weighted s (comm Q G) ≤ κ) (hQR : weighted s (comm Q R) ≤ κ) (a b : Fin 3) :
    weighted s (comm (ternaryEffect F Q a) (ternaryEffect G R b)) ≤ 4*κ := by
  have h1 := effect_comm_right s G R F κ hκ hFG hFR b
  have h2 := effect_comm_right s G R Q κ hκ hQG hQR b
  have h := effect_comm_left s F Q (ternaryEffect G R b) (2*κ) (by positivity) h1 h2 a
  linarith

theorem effect_state {d : ℕ} (s : State d) (F Q : Mat d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hF : hs (comm F s.xi) ≤ κ) (hQ : hs (comm Q s.xi) ≤ κ) (a : Fin 3) :
    hs (comm (ternaryEffect F Q a) s.xi) ≤ 2*κ := by
  fin_cases a
  · change hs (comm (1-F) s.xi) ≤ _
    rw [state_complement]; linarith
  · exact (state_sub s F Q).trans (by linarith)
  · exact hQ.trans (by linarith)

def ternarySwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem effect_own_conjugation {d : ℕ} (s : State d) (F Q U : Mat d)
    (hU : Domain.reflection.Holds U) (κ : ℝ) (hκ : 0 ≤ κ)
    (hF : weighted s (U*F*U-F) ≤ κ) (hQ : weighted s (U*Q*U-(F-Q)) ≤ κ) (a : Fin 3) :
    weighted s (U*ternaryEffect F Q a*U-ternaryEffect F Q (ternarySwap a)) ≤ 2*κ := by
  fin_cases a
  · have he : U*(1-F)*U-(1-F)= -(U*F*U-F) := by
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hU.2]; abel
    change weighted s (U*(1-F)*U-(1-F)) ≤ _
    rw [he,weighted_neg]; linarith
  · change weighted s (U*(F-Q)*U-Q) ≤ _
    have he : U*(F-Q)*U-Q=(U*F*U-F)-(U*Q*U-(F-Q)) := by noncomm_ring
    rw [he]; exact (weighted_sub s _ _).trans (by linarith)
  · exact hQ.trans (by linarith)

theorem effect_projection {d : ℕ} (F Q : Mat d) (hF : Domain.projection.Holds F)
    (hQ : Domain.projection.Holds Q) (hFQ : F*Q=Q) (a : Fin 3) :
    Domain.projection.Holds (ternaryEffect F Q a) := by
  let P := conditionalMeasurement F Q hF hQ hFQ
  have he : P.projection a=ternaryEffect F Q a := by fin_cases a <;> rfl
  exact he ▸ ⟨P.selfadjoint a,P.idempotent a⟩

theorem effect_own_intertwining {d : ℕ} (s : State d) (F Q U : Mat d)
    (hF : Domain.projection.Holds F) (hQ : Domain.projection.Holds Q) (hFQ : F*Q=Q)
    (hU : Domain.reflection.Holds U) (κ : ℝ) (hκ : 0 ≤ κ)
    (hσ : hs (comm U s.xi) ≤ κ) (hflag : weighted s (U*F*U-F) ≤ κ)
    (hdata : weighted s (U*Q*U-(F-Q)) ≤ κ) (a : Fin 3) :
    weighted s (U*ternaryEffect F Q a-ternaryEffect F Q (ternarySwap a)*U) ≤ 4*κ := by
  have hnU := (unitary_norm (state_dimension_pos s) (reflection_unitary U hU)).le
  let E := U*ternaryEffect F Q a*U-ternaryEffect F Q (ternarySwap a)
  have hE : weighted s E ≤ 2*κ := effect_own_conjugation s F Q U hU κ hκ hflag hdata a
  have hnE : ‖E‖ ≤ 2 := by
    have hnA := projection_norm_le (effect_projection F Q hF hQ hFQ a)
    have hnB := projection_norm_le (effect_projection F Q hF hQ hFQ (ternarySwap a))
    have hn1 := norm_mul_le U (ternaryEffect F Q a)
    have hn2 := norm_mul_le (U*ternaryEffect F Q a) U
    have hnUA : ‖U*ternaryEffect F Q a‖ ≤ 1 := by nlinarith [norm_nonneg U,norm_nonneg (ternaryEffect F Q a)]
    dsimp [E]; exact (norm_sub_le _ _).trans (by nlinarith [norm_nonneg U,norm_nonneg (U*ternaryEffect F Q a)])
  have he : U*ternaryEffect F Q a-ternaryEffect F Q (ternarySwap a)*U=E*U := by
    dsimp [E]; rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_assoc,hU.2,Matrix.mul_one]
  rw [he]
  have h := weighted_right s U E
  have h1 := mul_le_mul_of_nonneg_right hnU (weighted_nonneg s E)
  have h2 := mul_le_mul hnE hσ (hsNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  linarith

end
end E2
