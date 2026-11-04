import E2.ConditionalCommutations

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

/-- Recover a later conditional digit from the repaired tail, before moving
the computation to depth i. No own-bit-flip equation is needed for this bound. -/
theorem affine_tail_digit_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : AffineClockApprox s δ c) (r : SpectralRepair c s δ K)
    (Y : Mat d) (hnY : ‖Y‖≤1) (hσY : hs (comm Y s.xi)≤δ)
    (hYtail : weighted s (comm Y (c.T*c.A*c.T.conjTranspose))≤δ) (k : ℕ) :
    weighted s (comm Y (rawDigit c (k+1)))≤38*K*4^k*δ := by
  rcases hc with ⟨hA,hP,hT,_hAP,_hAff,_hσA,_hσP,hσT⟩
  have hK0 : 0≤K := by linarith
  have hδK : δ≤K*δ := by nlinarith only [mul_le_mul_of_nonneg_right hK hδ]
  have hclose : weighted s (r.Ahat-c.A)≤K*δ :=
    le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hnDiff : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans
    (by linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hA])
  let Z := translate c.T r.Ahat 1
  let D := translate c.T (r.Ahat-c.A) 1
  have hZ : HasCantorSpectrum Z := translate_cantor_spectrum c.T r.Ahat hT r.spectrum 1
  have hnD : ‖D‖≤2 := (translate_norm s c.T _ hT 1).trans hnDiff
  have hwD : weighted s D≤K*δ+2*δ := by
    have h := translate_weighted s c.T (r.Ahat-c.A) hT δ hδ hσT 1
    have hm := mul_le_mul_of_nonneg_right hnDiff hδ
    norm_num only [Nat.cast_one,one_mul] at h
    nlinarith only [h,hm,hclose]
  have hcD : weighted s (comm Y D)≤2*K*δ+6*δ := by
    have h := commutator_replace s D Y hnY
    rw [weighted_comm_symm] at h
    have hm := mul_le_mul hnD hσY (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    nlinarith only [h,hm,hwD]
  have hcommZ : weighted s (comm Y Z)≤9*K*δ := by
    have he : Z=translate c.T c.A 1+D := by
      dsimp [Z,D]
      rw [translate_sub]
      abel
    have ht : weighted s (comm Y (translate c.T c.A 1))≤δ := by simpa [translate] using hYtail
    rw [he,comm_add_right]
    have h := weighted_add s (comm Y (translate c.T c.A 1)) (comm Y D)
    nlinarith only [h,ht,hcD,hδK]
  have hσZ : hs (comm Z s.xi)≤3*K*δ := by
    have h := translated_state_commutator s (K*δ) c.T r.Ahat (mul_nonneg hK0 hδ) hT
      (cantor_matrix_norm r.spectrum) (hσT.trans hδK) hσA 1
    convert h using 1 <;> norm_num <;> ring
  let S := matrixFunction (digitAt k) Z
  have hfc : weighted s (comm Y S)≤30*K*4^k*δ := by
    have h := commutator_functional_calculus s Z Y (digitAt k) (2*4^k) hZ.1 hnY
      (digitAt_lipschitz k).lipschitzOnWith
    norm_num only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow] at h
    calc
      _≤(2*4^k)*(9*K*δ+2*(3*K*δ)) := h.trans (by gcongr)
      _=_ := by ring
  have hnRaw (q : ℕ) : ‖rawDigit c q‖≤1 := projection_norm_le (translate_projection c.T c.P hT hP q)
  have hnSpec : ‖matrixFunction (digitAt k) r.Ahat‖≤1 :=
    cantor_function_norm r.spectrum _ (fun x hx => cantor_digit_bounds k hx)
  have hnR : ‖rawDigit c k-matrixFunction (digitAt k) r.Ahat‖≤2 :=
    (norm_sub_le _ _).trans (by linarith [hnRaw k])
  have hDS : weighted s (rawDigit c (k+1)-S)≤K*4^k*δ+2*δ := by
    have h := translate_weighted s c.T (rawDigit c k-matrixFunction (digitAt k) r.Ahat) hT δ hδ hσT 1
    have he : translate c.T (rawDigit c k-matrixFunction (digitAt k) r.Ahat) 1=rawDigit c (k+1)-S := by
      rw [translate_sub,translate_matrix_function c.T r.Ahat hT r.spectrum.1]
      change translate c.T (translate c.T c.P k) 1-matrixFunction (digitAt k) Z=_
      rw [translate_add]
      rfl
    rw [he] at h
    have hm := mul_le_mul_of_nonneg_right hnR hδ
    have hd := r.digits k
    norm_num only [Nat.cast_one,one_mul] at h
    nlinarith only [h,hm,hd]
  have hnS : ‖S‖≤1 := cantor_function_norm hZ _ (fun x hx => cantor_digit_bounds k hx)
  have hnDS : ‖rawDigit c (k+1)-S‖≤2 := (norm_sub_le _ _).trans (by linarith [hnRaw (k+1)])
  have hcorr : weighted s (comm Y (rawDigit c (k+1)-S))≤2*K*4^k*δ+6*δ := by
    have h := commutator_replace s (rawDigit c (k+1)-S) Y hnY
    rw [weighted_comm_symm] at h
    have hm := mul_le_mul hnDS hσY (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    nlinarith only [h,hm,hDS]
  have he : comm Y (rawDigit c (k+1))=comm Y S+comm Y (rawDigit c (k+1)-S) := by
    simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul]
    abel
  rw [he]
  have h := weighted_add s (comm Y S) (comm Y (rawDigit c (k+1)-S))
  have hp : (1:ℝ)≤4^k := one_le_pow₀ (by norm_num)
  have hKp : (1:ℝ)≤K*4^k := by nlinarith only [hp,mul_le_mul_of_nonneg_right hK (show (0:ℝ)≤4^k by positivity)]
  have hδp := mul_le_mul_of_nonneg_right hKp hδ
  nlinarith only [h,hfc,hcorr,hδp]

theorem affine_translated_tail_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : AffineClockApprox s δ c) (r : SpectralRepair c s δ K)
    (Y : Mat d) (hnY : ‖Y‖≤1) (hσY : hs (comm Y s.xi)≤δ)
    (hYtail : weighted s (comm Y (c.T*c.A*c.T.conjTranspose))≤δ) (i j : ℕ) (hij : i<j) :
    weighted s (comm (translate c.T Y i) (rawDigit c j))≤38*K*4^(j-i-1)*δ+2*i*δ := by
  let k := j-i-1
  have hindex : k+1+i=j := by dsimp [k]; omega
  have hP := hc.2.1
  have hT := hc.2.2.1
  have hσT := hc.2.2.2.2.2.2.2
  let E := comm Y (rawDigit c (k+1))
  have hE : weighted s E≤38*K*4^k*δ := affine_tail_digit_commutator s δ K c hδ hK hc r Y hnY hσY hYtail k
  have hnE : ‖E‖≤2 := norm_comm_contractions _ _ hnY
    (projection_norm_le (translate_projection c.T c.P hT hP (k+1)))
  have he : translate c.T E i=comm (translate c.T Y i) (rawDigit c j) := by
    dsimp [E]
    rw [translate_comm c.T _ _ hT i]
    change comm (translate c.T Y i) (translate c.T (translate c.T c.P (k+1)) i)=_
    rw [translate_add,hindex]
    rfl
  have h := translate_weighted s c.T E hT δ hδ hσT i
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_right hnE (mul_nonneg (Nat.cast_nonneg i) hδ)
  nlinarith only [h,hE,hm]

end
end E2
