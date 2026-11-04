import E2.Carry
import E2.ClockExtras

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

def SpectralRepair.increase {d : ℕ} {s : State d} {δ K L : ℝ} {c : ClockData d}
    (r : SpectralRepair c s δ K) (hKL : K≤L) (hδ : 0≤δ) : SpectralRepair c s δ L where
  Ahat := r.Ahat
  spectrum := r.spectrum
  closeness := r.closeness.trans (mul_le_mul_of_nonneg_right hKL hδ)
  digits := fun j => (r.digits j).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKL (by positivity)) hδ)

/-- One conditional coordinate is spectrally recovered. The other operator
stays raw, so there is only one digit-depth loss. -/
theorem affine_digit_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : AffineClockApprox s δ c) (r : SpectralRepair c s δ K)
    (Y : Mat d) (hnY : ‖Y‖≤1) (hYA : weighted s (comm Y c.A)≤δ)
    (hσY : hs (comm Y s.xi)≤δ) (j : ℕ) :
    weighted s (comm Y (rawDigit c j))≤18*K*4^j*δ := by
  rcases hc with ⟨hA,hP,hT,_hAP,_hAff,_hσA,_hσP,_hσT⟩
  have hclose : weighted s (r.Ahat-c.A)≤K*δ :=
    le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hσ : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hnDiff : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans
    (by linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hA])
  have hrep := commutator_replace s (r.Ahat-c.A) Y hnY
  rw [weighted_comm_symm] at hrep
  have hmul := mul_le_mul hnDiff hσY (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hhat : weighted s (comm Y r.Ahat)≤(2*K+3)*δ := by
    have he : comm Y r.Ahat=comm Y c.A+comm Y (r.Ahat-c.A) := by
      simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul]
      abel
    rw [he]
    have h := weighted_add s (comm Y c.A) (comm Y (r.Ahat-c.A))
    nlinarith only [h,hrep,hmul,hclose,hYA]
  let S := matrixFunction (digitAt j) r.Ahat
  have hfc : weighted s (comm Y S)≤(8*K+6)*4^j*δ := by
    have h := commutator_functional_calculus s r.Ahat Y (digitAt j) (2*4^j)
      r.spectrum.1 hnY (digitAt_lipschitz j).lipschitzOnWith
    norm_num only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow] at h
    calc
      _≤(2*4^j)*((2*K+3)*δ+2*(K*δ)) := h.trans (by gcongr)
      _=_ := by ring
  have hnRaw : ‖rawDigit c j‖≤1 := projection_norm_le (translate_projection c.T c.P hT hP j)
  have hnS : ‖S‖≤1 := cantor_function_norm r.spectrum _ (fun x hx => cantor_digit_bounds j hx)
  have hnD : ‖rawDigit c j-S‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have hcorr : weighted s (comm Y (rawDigit c j-S))≤2*K*4^j*δ+2*δ := by
    have h := commutator_replace s (rawDigit c j-S) Y hnY
    rw [weighted_comm_symm] at h
    have hm := mul_le_mul hnD hσY (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    have hd : weighted s (rawDigit c j-S)≤K*4^j*δ := r.digits j
    nlinarith only [h,hm,hd]
  have he : comm Y (rawDigit c j)=comm Y S+comm Y (rawDigit c j-S) := by
    simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul]
    abel
  rw [he]
  have h := weighted_add s (comm Y S) (comm Y (rawDigit c j-S))
  have hp : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
  have hcoef : 10*K+6≤16*K := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef (show 0≤(4:ℝ)^j*δ by positivity)
  have hKp : (1:ℝ)≤K*4^j := by nlinarith only [hK,hp,mul_le_mul_of_nonneg_right hK (show (0:ℝ)≤4^j by positivity)]
  have hδp := mul_le_mul_of_nonneg_right hKp hδ
  nlinarith only [h,hfc,hcorr,hscaled,hδp]

theorem affine_translated_digit_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : AffineClockApprox s δ c) (r : SpectralRepair c s δ K)
    (Y : Mat d) (hnY : ‖Y‖≤1) (hYA : weighted s (comm Y c.A)≤δ)
    (hσY : hs (comm Y s.xi)≤δ) (i j : ℕ) (hij : i≤j) :
    weighted s (comm (translate c.T Y i) (rawDigit c j))≤18*K*4^(j-i)*δ+2*i*δ := by
  rcases hc with ⟨hA,hP,hT,hAP,hAff,hσA,hσP,hσT⟩
  let E := comm Y (rawDigit c (j-i))
  have hE : weighted s E≤18*K*4^(j-i)*δ :=
    affine_digit_commutator s δ K c hδ hK ⟨hA,hP,hT,hAP,hAff,hσA,hσP,hσT⟩ r Y hnY hYA hσY (j-i)
  have hnE : ‖E‖≤2 := norm_comm_contractions _ _ hnY
    (projection_norm_le (translate_projection c.T c.P hT hP (j-i)))
  have he : translate c.T E i=comm (translate c.T Y i) (rawDigit c j) := by
    dsimp [E]
    rw [translate_comm c.T _ _ hT i]
    change comm (translate c.T Y i) (translate c.T (translate c.T c.P (j-i)) i)=_
    rw [translate_add,Nat.sub_add_cancel hij]
    rfl
  have ht := translate_weighted s c.T E hT δ hδ hσT i
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_right hnE (mul_nonneg (Nat.cast_nonneg i) hδ)
  nlinarith only [ht,hE,hm]

end
end E2
