import E2.CountEntropyScalar

namespace E2
noncomputable section
set_option maxHeartbeats 200000

/-- An elementary global square-root modulus, with no differentiability at zero. -/
theorem neg_mul_log_sqrt_bound (x : ℝ) (hx : 0≤x) :
    Real.negMulLog x≤2*Real.sqrt x := by
  have h := Real.negMulLog_mul (Real.sqrt x) (Real.sqrt x)
  rw [Real.mul_self_sqrt hx] at h
  have hsmall : Real.negMulLog (Real.sqrt x)≤1 :=
    (Real.negMulLog_le_one_sub_self (Real.sqrt_nonneg x)).trans (by linarith [Real.sqrt_nonneg x])
  calc
    _ = 2*Real.sqrt x*Real.negMulLog (Real.sqrt x) := by linarith only [h]
    _ ≤ 2*Real.sqrt x*1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := mul_one _

/-- Quantitative control of the entropy term, sufficient even after multiplying
by a growing number of measurements. -/
theorem binary_entropy_sqrt_bound (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    binaryEntropy x ≤ 3*Real.sqrt x/Real.log 2 := by
  have hlog := neg_mul_log_sqrt_bound x hx
  have hcomp := Real.negMulLog_le_one_sub_self (show 0≤1-x by linarith)
  have hroot : x≤Real.sqrt x := by
    apply (sq_le_sq₀ hx (Real.sqrt_nonneg x)).mp
    rw [Real.sq_sqrt hx]
    nlinarith [mul_nonneg hx (show 0≤1-x by linarith)]
  unfold binaryEntropy
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith

end
end E2
