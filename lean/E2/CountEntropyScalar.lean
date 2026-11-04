import E2.MeasurementDefs

namespace E2
noncomputable section
set_option maxHeartbeats 200000

 theorem binary_entropy_left_chord (x : ℝ) (hx : 0≤x) (hxhalf : x≤1/2) :
    2*x≤binaryEntropy x := by
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ)∈Set.Icc 0 1 by norm_num)
    (show (2:ℝ)⁻¹∈Set.Icc 0 1 by norm_num)
    (show 0≤1-2*x by linarith) (show 0≤2*x by linarith)
    (show (1-2*x)+(2*x)=1 by ring)
  have he : (1-2*x)*(0:ℝ)+(2*x)*(2:ℝ)⁻¹=x := by ring
  simp only [smul_eq_mul,he,Real.binEntropy_zero,mul_zero,zero_add,Real.binEntropy_two_inv] at h
  have he2 : 2*x*(2:ℝ)⁻¹=x := by ring
  rw [he2] at h
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr h

/-- The binary imbalance inequality in Theorem 8.1, including deterministic laws. -/
 theorem binary_entropy_imbalance (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    1-|2*x-1|≤binaryEntropy x := by
  by_cases h : x≤1/2
  · rw [abs_of_nonpos (by linarith : 2*x-1≤0)]
    linarith [binary_entropy_left_chord x hx h]
  · have hother := binary_entropy_left_chord (1-x) (by linarith) (by linarith)
    simp only [binaryEntropy,Real.binEntropy_one_sub] at hother
    change 2*(1-x)≤binaryEntropy x at hother
    rw [abs_of_nonneg (by linarith : 0≤2*x-1)]
    linarith

/-- Entropy of two unnormalized masses. The zero-mass case is explicit. -/
 theorem binary_mass_entropy_log (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    (a+b)*binaryEntropy (a/(a+b)) =
      (Real.negMulLog a+Real.negMulLog b-Real.negMulLog (a+b))/Real.log 2 := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]
  have h1 : (a+b)*(a/(a+b))=a := mul_div_cancel₀ a hs
  have h2 : (a+b)*(1-a/(a+b))=b := by field_simp; ring
  have h := congrArg₂ (·+·) (Real.negMulLog_mul (a+b) (a/(a+b)))
    (Real.negMulLog_mul (a+b) (1-a/(a+b)))
  rw [h1,h2] at h
  rw [binaryEntropy,Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,←mul_div_assoc]
  congr 1
  linarith only [h]

 theorem binary_mass_imbalance (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    a+b-|a-b| ≤ (a+b)*binaryEntropy (a/(a+b)) := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]
  have hs0 : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have h := mul_le_mul_of_nonneg_left
    (binary_entropy_imbalance (a/(a+b)) (div_nonneg ha hs0.le)
      ((div_le_one hs0).mpr (by linarith))) hs0.le
  have he : (a+b)*|2*(a/(a+b))-1|=|a-b| := by
    calc
      _ = |(a+b)*(2*(a/(a+b))-1)| := by rw [abs_mul,abs_of_nonneg hs0.le]
      _ = _ := by congr 1; field_simp; ring
  rw [mul_sub,mul_one,he] at h
  exact h

/-- The exact ternary inequality used by the paper, retaining an inactive label. -/
 theorem ternary_entropy_imbalance (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (hnorm : a+b+c=1) :
    b+c-|b-c| ≤ (Real.negMulLog a+Real.negMulLog b+Real.negMulLog c)/Real.log 2 := by
  have h := binary_mass_imbalance b c hb hc
  rw [binary_mass_entropy_log b c hb hc] at h
  have hbc : b+c=1-a := by linarith
  have hnon : 0≤(Real.negMulLog a+Real.negMulLog (b+c))/Real.log 2 := by
    rw [hbc,←Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact div_nonneg (Real.binEntropy_nonneg ha (by linarith)) (Real.log_pos (by norm_num)).le
  simp only [add_div,sub_div] at h hnon ⊢
  linarith

end
end E2


