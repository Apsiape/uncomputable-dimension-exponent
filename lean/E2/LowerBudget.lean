import E2.LowerDepth
import E2.LowerEntropyModulus

namespace E2.Turn9
noncomputable section
open Filter
set_option maxHeartbeats 200000

 theorem depth_eventually_valid : ∀ᶠ t : ℝ in atTop,
    0≤t ∧ 0≤t-30*Real.logb 4 (2+t) := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    raw_depth_ratio.eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ)<1))] with t ht hr
  refine ⟨ht.le,?_⟩
  have h := (lt_div_iff₀ ht).mp hr
  linarith

/-- A deliberately coarser polynomial envelope sufficient for the lower theorem. -/
 theorem depth_joint_error_bound (t K : ℝ) (hK : 0≤K) (ht : 0≤t)
    (hr : 0≤t-30*Real.logb 4 (2+t)) :
    jointError (depth t) ((4:ℝ)^(-t)) K ≤ K/(2+t)^4 := by
  have hn : 1≤2+t := by linarith
  have hn0 : 0<2+t := by linarith
  have hlog : 0≤Real.logb 4 (2+t) := Real.logb_nonneg (by norm_num) (by linarith)
  have hd : (depth t:ℝ)≤t := (Nat.floor_le hr).trans (by linarith)
  have hsave : (4:ℝ)^(depth t)*(4:ℝ)^(-t)≤1/(2+t)^10 := by
    calc
      _≤(2+t)^(-30:ℝ) := depth_attenuation t hr hn0
      _≤(2+t)^(-10:ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _=1/(2+t)^10 := by
        norm_num [Real.rpow_neg,Real.rpow_natCast,one_div]
  unfold jointError
  calc
    _ = K*((depth t:ℝ)+1)^6*((4:ℝ)^(depth t)*(4:ℝ)^(-t)) := by push_cast; ring
    _ ≤ K*(2+t)^6*((4:ℝ)^(depth t)*(4:ℝ)^(-t)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hK
      exact pow_le_pow_left₀ (by positivity) (by linarith) 6
    _ ≤ K*(2+t)^6*(1/(2+t)^10) := mul_le_mul_of_nonneg_left hsave (by positivity)
    _ = K/(2+t)^4 := by
      rw [show (10:ℕ)=6+4 by decide,pow_add]
      field_simp

/-- Numerical envelope for the two polynomial error budgets, without an entropy premise. -/
 theorem count_budget_envelope (C K n η : ℝ) (M : ℕ)
    (hC : 0≤C) (hK : 0≤K) (hn : 0<n) (hM : (M:ℝ)≤n)
    (hη : 0≤η) (hηK : η≤K/n^4) :
    C*(4*M)^4*η^2≤256*C*K^2/n^4 ∧ C*(4*M)^3*η≤64*C*K/n := by
  constructor
  · calc
      _ ≤ C*(4*n)^4*(K/n^4)^2 := by gcongr
      _ = _ := by field_simp; ring
  · calc
      _ ≤ C*(4*n)^3*(K/n^4) := by gcongr
      _ = _ := by field_simp; ring

 theorem reciprocal_power_limit (A : ℝ) (k : ℕ) (hk : 0<k) :
    Tendsto (fun t : ℝ => A/(2+t)^k) atTop (nhds 0) := by
  have hn : Tendsto (fun t : ℝ => 2+t) atTop atTop :=
    tendsto_atTop_add_const_left atTop 2 tendsto_id
  have hp : Tendsto (fun t : ℝ => (2+t)^k) atTop atTop := by
    simpa only [Function.comp_def,Real.rpow_natCast] using
      (tendsto_rpow_atTop (by exact_mod_cast hk : (0:ℝ)<k)).comp hn
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using (tendsto_inv_atTop_zero.comp hp).const_mul A

/-- Both the decoding error and the direct polynomial loss vanish at the exact depth. -/
 theorem depth_budget_limits (C K : ℝ) (hC : 0<C) (hK : 0<K) :
    Tendsto (fun t : ℝ => C*(4*depth t)^4*(jointError (depth t) ((4:ℝ)^(-t)) K)^2)
      atTop (nhds 0) ∧
    Tendsto (fun t : ℝ => C*(4*depth t)^3*jointError (depth t) ((4:ℝ)^(-t)) K)
      atTop (nhds 0) := by
  have hbounds : ∀ᶠ t : ℝ in atTop,
      C*(4*depth t)^4*(jointError (depth t) ((4:ℝ)^(-t)) K)^2≤256*C*K^2/(2+t)^4 ∧
      C*(4*depth t)^3*jointError (depth t) ((4:ℝ)^(-t)) K≤64*C*K/(2+t) := by
    filter_upwards [depth_eventually_valid] with t ht
    have hlog : 0≤Real.logb 4 (2+t) := Real.logb_nonneg (by norm_num) (by linarith)
    have hd : (depth t:ℝ)≤2+t := (Nat.floor_le ht.2).trans (by linarith)
    exact count_budget_envelope C K (2+t) _ (depth t) hC.le hK.le (by linarith)
      hd (by unfold jointError; positivity) (depth_joint_error_bound t K hK.le ht.1 ht.2)
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun t => by positivity))
      (hbounds.mono (fun t h => h.1))
      (reciprocal_power_limit (256*C*K^2) 4 (by decide))
  · apply squeeze_zero' (Eventually.of_forall (fun t => by unfold jointError; positivity))
      (hbounds.mono (fun t h => h.2))
    simpa using reciprocal_power_limit (64*C*K) 1 (by decide)

/-- Normalized count penalty: sufficient for the epsilon-delta UniformLower type.
This does not assert the stronger unnormalized o(1) specification. -/
 theorem normalized_count_penalty (C K : ℝ) (hC : 0<C) (hK : 0<K) :
    Tendsto (fun t : ℝ => countPenalty C (depth t)
      (jointError (depth t) ((4:ℝ)^(-t)) K)/t) atTop (nhds 0) := by
  obtain ⟨he,hdirect⟩ := depth_budget_limits C K hC hK
  have hb : Tendsto (fun t : ℝ => binaryEntropy
      (C*(4*depth t)^4*(jointError (depth t) ((4:ℝ)^(-t)) K)^2)) atTop (nhds 0) := by
    simpa only [Function.comp_def,binaryEntropy,Real.binEntropy_zero,zero_div] using
      (Real.binEntropy_continuous.continuousAt.tendsto.comp he).div_const (Real.log 2)
  have hratio : Tendsto (fun t : ℝ => (4*(depth t:ℝ))/t) atTop (nhds 4) := by
    simpa only [mul_div_assoc,mul_one] using depth_ratio.const_mul 4
  have h := (hdirect.mul tendsto_inv_atTop_zero).add (hratio.mul (hb.add he))
  simp only [mul_zero,zero_add,zero_mul] at h
  convert h using 1
  ext t
  dsimp [countPenalty]
  ring

end
end E2.Turn9


