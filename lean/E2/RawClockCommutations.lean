import E2.RawClockTools

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

theorem spectral_functions_commute {d : ℕ} (A : Mat d) (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    comm (matrixFunction f A) (matrixFunction g A)=0 := by
  apply sub_eq_zero.mpr
  rw [matrix_function_mul,matrix_function_mul]
  apply matrix_function_congr hA
  intro x hx
  exact mul_comm _ _

theorem raw_digit_pair_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K) (j k : ℕ) :
    weighted s (comm (rawDigit c j) (rawDigit c k))≤
      6*K*4^j*δ+2*K*4^k*δ+(4*(k:ℝ)+2)*δ := by
  let qj := matrixFunction (digitAt j) r.Ahat
  let qk := matrixFunction (digitAt k) r.Ahat
  let Dj := rawDigit c j-qj
  let Dk := rawDigit c k-qk
  have hnRaw (i : ℕ) : ‖rawDigit c i‖≤1 :=
    projection_norm_le (translate_projection c.T c.P hc.1.2.2.1 hc.1.2.1 i)
  have hnq (i : ℕ) : ‖matrixFunction (digitAt i) r.Ahat‖≤1 :=
    cantor_function_norm r.spectrum (digitAt i) (fun x hx => cantor_digit_bounds i hx)
  have hnDj : ‖Dj‖≤2 := (norm_sub_le _ _).trans (by linarith [hnRaw j,hnq j])
  have hnDk : ‖Dk‖≤2 := (norm_sub_le _ _).trans (by linarith [hnRaw k,hnq k])
  have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hσq : hs (comm qj s.xi)≤2*4^j*K*δ := by
    have h := state_functional_calculus s r.Ahat (digitAt j) (2*4^j) r.spectrum.1 (digitAt_lipschitz j).lipschitzOnWith
    norm_num only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow] at h
    calc
      _≤(2*4^j)*hs (comm r.Ahat s.xi) := h
      _≤(2*4^j)*(K*δ) := by gcongr
      _=_ := by ring
  have hσraw := (raw_clock_state_commutators s δ c hδ hc k).1
  have hfirst : weighted s (comm Dj (rawDigit c k))≤2*K*4^j*δ+(4*(k:ℝ)+2)*δ := by
    have h := commutator_replace s Dj (rawDigit c k) (hnRaw k)
    have hm := mul_le_mul hnDj hσraw (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have he : weighted s Dj≤K*4^j*δ := r.digits j
    nlinarith only [h,hm,he]
  have hsecond : weighted s (comm qj Dk)≤2*K*4^k*δ+4*K*4^j*δ := by
    have h := commutator_replace s Dk qj (hnq j)
    have hm := mul_le_mul hnDk hσq (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have he : weighted s Dk≤K*4^k*δ := r.digits k
    rw [weighted_comm_symm]
    nlinarith only [h,hm,he]
  have he : comm (rawDigit c j) (rawDigit c k)=comm Dj (rawDigit c k)+comm qj Dk := by
    have h := commutator_two_replacements qj qk Dj Dk
    have hj : qj+Dj=rawDigit c j := by dsimp [Dj]; abel
    have hk : qk+Dk=rawDigit c k := by dsimp [Dk]; abel
    rw [hj,hk,spectral_functions_commute r.Ahat r.spectrum.1 _ _,add_zero] at h
    exact h
  rw [he]
  have h := weighted_add s (comm Dj (rawDigit c k)) (comm qj Dk)
  nlinarith only [h,hfirst,hsecond]

theorem raw_flip_tail_commutator {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hc : ClockApprox s δ c) (j : ℕ) :
    weighted s (comm (rawFlip c j) (translate c.T c.A (j+1)))≤(2*(j:ℝ)+1)*δ := by
  have hT := hc.1.2.2.1
  have hXu := reflection_unitary c.X hc.1.2.2.2
  have hnX : ‖c.X‖≤1 := (unitary_norm (state_dimension_pos s) hXu).le
  have hnB : ‖c.T*c.A*c.T.conjTranspose‖≤1 := by
    have h := (translate_norm s c.T c.A hT 1).trans (positive_contraction_norm hc.1.1)
    simpa only [translate,pow_one] using h
  let E := comm c.X (c.T*c.A*c.T.conjTranspose)
  have hnE : ‖E‖≤2 := norm_comm_contractions _ _ hnX hnB
  have hE : weighted s E≤δ := hc.2.1 _ (by simp [ClockData.defects,E])
  have htail : translate c.T (c.T*c.A*c.T.conjTranspose) j=translate c.T c.A (j+1) := by
    have h := translate_add c.T c.A 1 j
    rw [show 1+j=j+1 by omega] at h
    simpa only [translate,pow_one] using h
  have ht := translate_weighted s c.T E hT δ hδ (hc.2.2 c.T (by simp [ClockData.variables])) j
  have he : translate c.T E j=comm (rawFlip c j) (translate c.T c.A (j+1)) := by
    dsimp [E]
    rw [translate_comm c.T _ _ hT j,htail]
    rfl
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_right hnE (mul_nonneg (Nat.cast_nonneg j) hδ)
  nlinarith only [ht,hE,hm]

end
end E2

#print axioms E2.spectral_functions_commute
#print axioms E2.raw_digit_pair_commutator
#print axioms E2.raw_flip_tail_commutator
