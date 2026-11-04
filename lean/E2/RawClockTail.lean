import E2.RawClockCommutations

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 400000

theorem translate_cantor_spectrum {d : ℕ} (T A : Mat d) (hT : Domain.unitary.Holds T)
    (hA : HasCantorSpectrum A) (i : ℕ) : HasCantorSpectrum (translate T A i) := by
  refine ⟨translate_hermitian T A hA.1 i,?_⟩
  rw [translate_eq_conjugate,unitary_conjugate_spectrum _ _ (unitary_power hT i)]
  exact hA.2

/-- A flip is compared with a translated repaired tail before any later digit
function is applied. The correction is paid additively on the original state. -/
theorem repaired_tail_flip_bounds {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K) (j : ℕ) :
    weighted s (comm (rawFlip c j) (translate c.T r.Ahat (j+1)))≤(2*K+10*(j:ℝ)+7)*δ ∧
    hs (comm (translate c.T r.Ahat (j+1)) s.xi)≤(2*(j:ℝ)+3)*K*δ := by
  have hT := hc.1.2.2.1
  have hσT := hc.2.2 c.T (by simp [ClockData.variables])
  have hσX := (raw_clock_state_commutators s δ c hδ hc j).2
  have hX := translate_reflection c.T c.X hT hc.1.2.2.2 j
  have hnX : ‖rawFlip c j‖≤1 := (unitary_norm (state_dimension_pos s) (reflection_unitary _ hX)).le
  let Z := translate c.T (r.Ahat-c.A) (j+1)
  have hnDiff : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans (by
    linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hc.1.1])
  have hnZ : ‖Z‖≤2 := (translate_norm s c.T _ hT (j+1)).trans hnDiff
  have hclose : weighted s (r.Ahat-c.A)≤K*δ := le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hmove := translate_weighted s c.T (r.Ahat-c.A) hT δ hδ hσT (j+1)
  have hwZ : weighted s Z≤K*δ+2*((j:ℝ)+1)*δ := by
    have hm := mul_le_mul_of_nonneg_right hnDiff (mul_nonneg (Nat.cast_nonneg (j+1)) hδ)
    push_cast at hmove hm
    nlinarith only [hmove,hm,hclose]
  have hcommZ : weighted s (comm (rawFlip c j) Z)≤(2*K+8*(j:ℝ)+6)*δ := by
    have h := commutator_replace s Z (rawFlip c j) hnX
    have hm := mul_le_mul hnZ hσX (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    rw [weighted_comm_symm]
    nlinarith only [h,hm,hwZ]
  have hraw := raw_flip_tail_commutator s δ c hδ hc j
  have he : translate c.T r.Ahat (j+1)=translate c.T c.A (j+1)+Z := by
    dsimp [Z]
    rw [translate_sub]
    abel
  constructor
  · rw [he,comm_add_right]
    have h := weighted_add s (comm (rawFlip c j) (translate c.T c.A (j+1))) (comm (rawFlip c j) Z)
    nlinarith only [h,hraw,hcommZ]
  · have hK0 : 0≤K := by linarith
    have hδK : δ≤K*δ := by nlinarith
    have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
      le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
    have h := translated_state_commutator s (K*δ) c.T r.Ahat (mul_nonneg hK0 hδ)
      hT (cantor_matrix_norm r.spectrum) (hσT.trans hδK) hσA (j+1)
    push_cast at h
    convert h using 1 <;> ring

theorem translated_digit_repair {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K)
    (j k : ℕ) (hjk : j<k) :
    weighted s (rawDigit c k-matrixFunction (digitAt (k-j-1)) (translate c.T r.Ahat (j+1)))≤
      K*4^(k-j-1)*δ+2*((j:ℝ)+1)*δ := by
  let q := k-j-1
  have hindex : q+(j+1)=k := by dsimp [q]; omega
  have hT := hc.1.2.2.1
  have hnRaw : ‖rawDigit c q‖≤1 := projection_norm_le (translate_projection c.T c.P hT hc.1.2.1 q)
  have hnSpec : ‖matrixFunction (digitAt q) r.Ahat‖≤1 :=
    cantor_function_norm r.spectrum _ (fun x hx => cantor_digit_bounds q hx)
  have hn : ‖rawDigit c q-matrixFunction (digitAt q) r.Ahat‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have ht := translate_weighted s c.T (rawDigit c q-matrixFunction (digitAt q) r.Ahat) hT δ hδ
    (hc.2.2 c.T (by simp [ClockData.variables])) (j+1)
  have he : translate c.T (rawDigit c q-matrixFunction (digitAt q) r.Ahat) (j+1)=
      rawDigit c k-matrixFunction (digitAt q) (translate c.T r.Ahat (j+1)) := by
    change translate c.T (translate c.T c.P q-matrixFunction (digitAt q) r.Ahat) (j+1)=_
    rw [translate_sub,translate_add,hindex,translate_matrix_function c.T r.Ahat hT r.spectrum.1]
    rfl
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_right hn (mul_nonneg (Nat.cast_nonneg (j+1)) hδ)
  push_cast at ht hm
  have hr := r.digits q
  nlinarith only [ht,hm,hr]

theorem raw_later_digit_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K)
    (j k : ℕ) (hjk : j<k) :
    weighted s (comm (rawFlip c j) (rawDigit c k))≤(36*(j:ℝ)+38)*K*4^(k-j-1)*δ := by
  let q := k-j-1
  let Z := translate c.T r.Ahat (j+1)
  let Y := matrixFunction (digitAt q) Z
  let D := rawDigit c k-Y
  have hT := hc.1.2.2.1
  have hZ : HasCantorSpectrum Z := translate_cantor_spectrum c.T r.Ahat hT r.spectrum (j+1)
  have hX := translate_reflection c.T c.X hT hc.1.2.2.2 j
  have hnX : ‖rawFlip c j‖≤1 := (unitary_norm (state_dimension_pos s) (reflection_unitary _ hX)).le
  have hσX := (raw_clock_state_commutators s δ c hδ hc j).2
  have hb := repaired_tail_flip_bounds s δ K c hδ hK hc r j
  have hcK : weighted s (comm (rawFlip c j) Z)≤(10*(j:ℝ)+9)*K*δ := by
    have hm := mul_le_mul_of_nonneg_left hK (show (0:ℝ)≤10*(j:ℝ)+7 by positivity)
    have hcoef : 2*K+10*(j:ℝ)+7≤(10*(j:ℝ)+9)*K := by nlinarith only [hm]
    exact hb.1.trans (by nlinarith only [mul_le_mul_of_nonneg_right hcoef hδ])
  have hfc : weighted s (comm (rawFlip c j) Y)≤(28*(j:ℝ)+30)*K*4^q*δ := by
    have h := commutator_functional_calculus s Z (rawFlip c j) (digitAt q) (2*4^q) hZ.1 hnX
      (digitAt_lipschitz q).lipschitzOnWith
    norm_num only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow] at h
    calc
      _≤(2*4^q)*((10*(j:ℝ)+9)*K*δ+2*((2*(j:ℝ)+3)*K*δ)) := h.trans (by gcongr; exact hb.2)
      _=_ := by ring
  have hnRaw : ‖rawDigit c k‖≤1 := projection_norm_le (translate_projection c.T c.P hT hc.1.2.1 k)
  have hnY : ‖Y‖≤1 := cantor_function_norm hZ _ (fun x hx => cantor_digit_bounds q hx)
  have hnD : ‖D‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have hclose : weighted s D≤K*4^q*δ+2*((j:ℝ)+1)*δ := translated_digit_repair s δ K c hδ hc r j k hjk
  have hcorr : weighted s (comm (rawFlip c j) D)≤2*K*4^q*δ+(8*(j:ℝ)+6)*δ := by
    have h := commutator_replace s D (rawFlip c j) hnX
    have hm := mul_le_mul hnD hσX (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    rw [weighted_comm_symm]
    nlinarith only [h,hm,hclose]
  have he : comm (rawFlip c j) (rawDigit c k)=comm (rawFlip c j) Y+comm (rawFlip c j) D := by
    have hsum : rawDigit c k=Y+D := by dsimp [D]; abel
    rw [hsum,comm_add_right]
  rw [he]
  have h := weighted_add s (comm (rawFlip c j) Y) (comm (rawFlip c j) D)
  have hpow : (1:ℝ)≤4^q := one_le_pow₀ (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hK (show (0:ℝ)≤4^q by positivity)
  have hkpow : (1:ℝ)≤K*4^q := by nlinarith only [hpow,hm]
  have hδpow := mul_le_mul_of_nonneg_right hkpow hδ
  have hcoeff := mul_le_mul_of_nonneg_left hδpow (show (0:ℝ)≤8*(j:ℝ)+6 by positivity)
  nlinarith only [h,hfc,hcorr,hcoeff]

end
end E2

#print axioms E2.translate_cantor_spectrum
#print axioms E2.repaired_tail_flip_bounds
#print axioms E2.translated_digit_repair
#print axioms E2.raw_later_digit_commutator
