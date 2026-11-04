import E2.Turn9.LowerStatements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor

namespace E2.Turn9
noncomputable section
open Filter
set_option maxHeartbeats 200000

/-- The logarithmic depth loss is sublinear, including the exact translated argument. -/
theorem depth_log_ratio : Tendsto (fun t : ℝ => Real.logb 4 (2+t)/t) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b:=4) 1 (-2) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_left atTop 2 tendsto_id)
  simp only [Function.comp_apply,id_eq,pow_one,one_mul] at h
  convert h using 1
  ext t
  congr 1 <;> ring

 theorem raw_depth_ratio : Tendsto (fun t : ℝ => (t-30*Real.logb 4 (2+t))/t) atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub (depth_log_ratio.const_mul 30)
  have h' : Tendsto (fun t : ℝ => 1-30*(Real.logb 4 (2+t)/t)) atTop (nhds 1) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  field_simp

/-- The exact floor in the paper retains asymptotic depth one. -/
theorem depth_ratio : Tendsto (fun t : ℝ => (depth t : ℝ)/t) atTop (nhds 1) := by
  have hevent : ∀ᶠ t : ℝ in atTop, 0<t ∧ 0≤t-30*Real.logb 4 (2+t) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),raw_depth_ratio.eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ)<1))] with t ht hr
    refine ⟨ht,?_⟩
    have hr' := (lt_div_iff₀ ht).mp hr
    linarith
  have hlo : Tendsto (fun t : ℝ => ((t-30*Real.logb 4 (2+t))-1)/t) atTop (nhds 1) := by
    have h := raw_depth_ratio.sub tendsto_inv_atTop_zero
    simpa only [sub_div,one_div,sub_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo raw_depth_ratio
  · filter_upwards [hevent] with t ht
    apply (div_le_div_iff_of_pos_right ht.1).mpr
    have h := Nat.lt_floor_add_one (t-30*Real.logb 4 (2+t))
    dsimp [depth]
    linarith
  · filter_upwards [hevent] with t ht
    exact (div_le_div_iff_of_pos_right ht.1).mpr (Nat.floor_le ht.2)

/-- Exact exponential saving at the paper's chosen depth. -/
theorem depth_attenuation (t : ℝ) (ht : 0≤t-30*Real.logb 4 (2+t)) (ht2 : 0<2+t) :
    (4:ℝ)^(depth t)*(4:ℝ)^(-t) ≤ (2+t)^(-30:ℝ) := by
  have hfloor : (depth t:ℝ)≤t-30*Real.logb 4 (2+t) := Nat.floor_le ht
  calc
    _ = (4:ℝ)^((depth t:ℝ)-t) := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ)<4),Real.rpow_natCast,Real.rpow_neg (by norm_num : (0:ℝ)≤4)]
      rfl
    _ ≤ (4:ℝ)^(-30*Real.logb 4 (2+t)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2+t)^(-30:ℝ) := by
      rw [mul_comm (-30:ℝ),Real.rpow_mul (by norm_num : (0:ℝ)≤4),Real.rpow_logb (by norm_num) (by norm_num) ht2]

end
end E2.Turn9


