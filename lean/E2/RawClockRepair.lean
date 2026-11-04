import E2.RawClockTail

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

def rawClockScale (K : ℝ) (M : ℕ) (δ : ℝ) : ℝ := K*((M:ℝ)+1)^3*(4:ℝ)^M*δ

theorem raw_clock_scale_bounds (K δ : ℝ) (M : ℕ) (hδ : 0≤δ) (hK : 1≤K) :
    0≤rawClockScale K M δ ∧
    (∀ i : ℕ, i≤M → K*4^i*δ≤rawClockScale K M δ) ∧
    (∀ i : ℕ, i≤M → (4*(i:ℝ)+2)*δ≤6*rawClockScale K M δ) ∧
    (∀ i : ℕ, i≤M → (2*(i:ℝ)+1)*δ≤3*rawClockScale K M δ) ∧
    (∀ i q : ℕ, i≤M → q≤M → (36*(i:ℝ)+38)*K*4^q*δ≤100*rawClockScale K M δ) := by
  have hK0 : 0≤K := by linarith
  have hM0 : (0:ℝ)≤M := Nat.cast_nonneg M
  have hp : (M:ℝ)+1≤((M:ℝ)+1)^3 := by
    have h : (0:ℝ)≤(M:ℝ)*(M+1)*(M+2) := by positivity
    nlinarith only [h]
  have hp1 : (1:ℝ)≤((M:ℝ)+1)^3 := by linarith
  have hfour : (1:ℝ)≤4^M := one_le_pow₀ (by norm_num : (1:ℝ)≤4)
  have hlin : ((M:ℝ)+1)*δ≤rawClockScale K M δ := by
    have hcoef : (M:ℝ)+1≤K*((M:ℝ)+1)^3*4^M := by
      calc
        _≤((M:ℝ)+1)^3 := hp
        _≤K*((M:ℝ)+1)^3 := by simpa using mul_le_mul_of_nonneg_right hK (show (0:ℝ)≤((M:ℝ)+1)^3 by positivity)
        _≤K*((M:ℝ)+1)^3*4^M := by simpa using mul_le_mul_of_nonneg_left hfour (show (0:ℝ)≤K*((M:ℝ)+1)^3 by positivity)
    exact mul_le_mul_of_nonneg_right hcoef hδ
  refine ⟨by unfold rawClockScale; positivity,?_,?_,?_,?_⟩
  · intro i hi
    have hpow : (4:ℝ)^i≤4^M := pow_le_pow_right₀ (by norm_num) hi
    change K*4^i*δ≤K*((M:ℝ)+1)^3*4^M*δ
    calc
      _≤K*4^M*δ := by gcongr
      _=(K*1)*4^M*δ := by ring
      _≤_ := by gcongr
  · intro i hi
    have hir : (i:ℝ)≤M := by exact_mod_cast hi
    have hcoef : 4*(i:ℝ)+2≤6*((M:ℝ)+1) := by linarith
    have h := mul_le_mul_of_nonneg_right hcoef hδ
    nlinarith only [h,hlin]
  · intro i hi
    have hir : (i:ℝ)≤M := by exact_mod_cast hi
    have hcoef : 2*(i:ℝ)+1≤3*((M:ℝ)+1) := by linarith
    have h := mul_le_mul_of_nonneg_right hcoef hδ
    nlinarith only [h,hlin]
  · intro i q hi hq
    have hir : (i:ℝ)≤M := by exact_mod_cast hi
    have hcoef : 36*(i:ℝ)+38≤100*((M:ℝ)+1)^3 := by nlinarith
    have hpow : (4:ℝ)^q≤4^M := pow_le_pow_right₀ (by norm_num) hq
    calc
      _≤(100*((M:ℝ)+1)^3)*K*4^M*δ := by gcongr
      _=100*rawClockScale K M δ := by unfold rawClockScale; ring

/-- Every raw-digit clause of Lemma 4.2 from the now-constructed spectral data.
The single scale is uniform in dimension, state, accuracy, and depth. -/
theorem raw_clock_estimates {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K) (M : ℕ) :
    (∀ j<M, Domain.projection.Holds (rawDigit c j)) ∧
    (∀ j<M, Domain.reflection.Holds (rawFlip c j)) ∧
    (∀ j<M, ∀ k<M, weighted s (comm (rawDigit c j) (rawDigit c k))≤100*rawClockScale K M δ) ∧
    (∀ j<M, weighted s (rawFlip c j*rawDigit c j*rawFlip c j-(1-rawDigit c j))≤100*rawClockScale K M δ) ∧
    (∀ j<M, ∀ k<M, j<k → weighted s (comm (rawFlip c j) (rawDigit c k))≤100*rawClockScale K M δ) ∧
    (∀ j<M, hs (comm (rawDigit c j) s.xi)≤100*rawClockScale K M δ) ∧
    (∀ j<M, hs (comm (rawFlip c j) s.xi)≤100*rawClockScale K M δ) := by
  obtain ⟨hscale,hp,h4,h2,hLater⟩ := raw_clock_scale_bounds K δ M hδ hK
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact translate_projection c.T c.P hc.1.2.2.1 hc.1.2.1 j
  · intro j hj
    exact translate_reflection c.T c.X hc.1.2.2.1 hc.1.2.2.2 j
  · intro j hj k hk
    have h := raw_digit_pair_commutator s δ K c hδ hc r j k
    have h1 := hp j (Nat.le_of_lt hj)
    have h2 := hp k (Nat.le_of_lt hk)
    have h3 := h4 k (Nat.le_of_lt hk)
    nlinarith only [h,h1,h2,h3,hscale]
  · intro j hj
    have h := raw_own_bit_flip s δ c hδ hc j
    have hn := h2 j (Nat.le_of_lt hj)
    linarith
  · intro j hj k hk hjk
    exact (raw_later_digit_commutator s δ K c hδ hK hc r j k hjk).trans
      (hLater j (k-j-1) (Nat.le_of_lt hj) (by omega))
  · intro j hj
    have h := (raw_clock_state_commutators s δ c hδ hc j).1
    have hn := h2 j (Nat.le_of_lt hj)
    linarith
  · intro j hj
    have h := (raw_clock_state_commutators s δ c hδ hc j).2
    have hn := h2 j (Nat.le_of_lt hj)
    linarith

end
end E2

#print axioms E2.rawClockScale
#print axioms E2.raw_clock_scale_bounds
#print axioms E2.raw_clock_estimates
