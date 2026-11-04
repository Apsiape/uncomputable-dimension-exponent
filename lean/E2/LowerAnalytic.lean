import E2.LowerBudget
import E2.LowerFinite

namespace E2
noncomputable section
open Filter
open Turn9
set_option maxHeartbeats 300000

 theorem real_precision_tendsto : Tendsto (fun t : ℝ => (4:ℝ)^(-t)) atTop
    (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := tendsto_rpow_atTop_of_base_lt_one ((4:ℝ)⁻¹) (by norm_num) (by norm_num)
    convert h using 1
    ext t
    rw [Real.inv_rpow (by norm_num : (0:ℝ)≤4),Real.rpow_neg (by norm_num : (0:ℝ)≤4)]
  · exact Eventually.of_forall (fun t => by simp only [Set.mem_Ioi]; positivity)

 theorem polynomial_precision_limit : Tendsto (fun t : ℝ => t^2*(4:ℝ)^(-t)) atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (Real.log 4)
    (Real.log_pos (by norm_num))
  convert h using 1
  ext t
  rw [Real.rpow_two,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<4)]
  congr 2
  ring

 theorem depth_transport_limit : Tendsto (fun t : ℝ => 2*(depth t:ℝ)^2*(4:ℝ)^(-t))
    atTop (nhds 0) := by
  have hu : Tendsto (fun t : ℝ => 2*t^2*(4:ℝ)^(-t)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_assoc] using polynomial_precision_limit.const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun t => by positivity)) _ hu
  filter_upwards [depth_eventually_valid] with t ht
  have hlog : 0≤Real.logb 4 (2+t) := Real.logb_nonneg (by norm_num) (by linarith)
  have hd : (depth t:ℝ)≤t := (Nat.floor_le ht.2).trans (by linarith)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2) (show (0:ℝ)≤2 by norm_num))
    (by positivity)

/-- The complete epsilon-delta analytic assembly, with the same flag, count
and joint-family inputs as the original lower_from_measurements statement. -/
theorem uniform_lower_analytic (p : CounterProgram) (ω : ℝ → ℝ)
    (hω : Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hflag : ∀ (δ : ℝ) (d : ℕ) (m : Model (sourcePresentation p) d δ), 0<δ →
      thetaK-ω δ≤expectation m.state (modelValue m 18))
    (C K : ℝ) (hC : 0<C) (hK : 0<K)
    (count : ∀ (d m : ℕ) (s : State d) (η : ℝ) (P : Fin m → Measurement d) (u : Fin m → Mat d),
      0<d → 0≤η → TriangularRelations s η P u → C*m^4*η^2≤1/2 →
      Real.logb 2 d≥binaryCount P+activeSum s P-C*m^3*η-
        m*(binaryEntropy (C*m^4*η^2)+C*m^4*η^2))
    (joint : ∀ (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ),
      1≤M → 0≤δ → Nonempty (JointFamily m M K)) :
    ∀ γ : ℝ, 0<γ → ∃ δ₀ : ℝ, 0<δ₀ ∧
      ∀ (δ : ℝ) (d : ℕ) (_m : Model (sourcePresentation p) d δ), 0<δ → δ<δ₀ →
        (3+thetaK-γ)*Real.logb 4 (1/δ)≤Real.logb 2 d := by
  have hωt : Tendsto (fun t : ℝ => ω ((4:ℝ)^(-t))) atTop (nhds 0) := hω.comp real_precision_tendsto
  have htransport : Tendsto (fun t : ℝ => 2*(depth t:ℝ)^2*(4:ℝ)^(-t)/t) atTop (nhds 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using depth_transport_limit.mul tendsto_inv_atTop_zero
  have hL : Tendsto (fun t : ℝ =>
      (3+thetaK-ω ((4:ℝ)^(-t)))*((depth t:ℝ)/t) -
      2*(depth t:ℝ)^2*(4:ℝ)^(-t)/t -
      countPenalty C (depth t) (jointError (depth t) ((4:ℝ)^(-t)) K)/t)
      atTop (nhds (3+thetaK)) := by
    simpa only [sub_zero,mul_one] using
      ((((tendsto_const_nhds (x := (3+thetaK))).sub hωt).mul depth_ratio).sub htransport).sub
        (normalized_count_penalty C K hC hK)
  have hM : ∀ᶠ t : ℝ in atTop, 1≤depth t := by
    filter_upwards [eventually_ge_atTop (2:ℝ),
      depth_ratio.eventually (Ioi_mem_nhds (by norm_num : (1/2:ℝ)<1))] with t ht hr
    have hdiv := (lt_div_iff₀ (by linarith : 0<t)).mp hr
    have hnat : (1:ℝ)≤(depth t:ℝ) := by linarith
    exact_mod_cast hnat
  have he := (depth_budget_limits C K hC hK).1.eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  intro γ hγ
  have hgood : ∀ᶠ t : ℝ in atTop,
      0<t ∧ 1≤depth t ∧
      C*(4*depth t)^4*(jointError (depth t) ((4:ℝ)^(-t)) K)^2≤1/2 ∧
      3+thetaK-γ≤(3+thetaK-ω ((4:ℝ)^(-t)))*((depth t:ℝ)/t) -
        2*(depth t:ℝ)^2*(4:ℝ)^(-t)/t-
        countPenalty C (depth t) (jointError (depth t) ((4:ℝ)^(-t)) K)/t := by
    filter_upwards [eventually_gt_atTop (0:ℝ),hM,he,
      hL.eventually (Ioi_mem_nhds (by linarith : 3+thetaK-γ<3+thetaK))] with t ht hm herr hl
    exact ⟨ht,hm,herr.le,hl.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hgood
  refine ⟨(4:ℝ)^(-max T 1),by positivity,?_⟩
  intro δ d m hδ hδsmall
  let t := Real.logb 4 (1/δ)
  have htdef : t= -Real.logb 4 δ := by simp only [t,one_div,Real.logb_inv]
  have hδeq : (4:ℝ)^(-t)=δ := by
    rw [htdef,neg_neg,Real.rpow_logb (by norm_num) (by norm_num) hδ]
  have hlogδ := Real.logb_lt_logb (by norm_num : (1:ℝ)<4) hδ hδsmall
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at hlogδ
  have htT : T≤t := by rw [htdef]; linarith [le_max_left T (1:ℝ)]
  obtain ⟨ht,hm,herr,hvalue⟩ := hT t htT
  obtain ⟨r⟩ := joint d (depth t) δ m hm hδ.le
  have hfinite := joint_count_lower p C K hC hK count d (depth t) δ m r hδ.le
    (by simpa only [hδeq] using herr)
  have hf := mul_le_mul_of_nonneg_right (hflag δ d m hδ) (Nat.cast_nonneg (depth t))
  have hbound : (3+thetaK-ω δ)*(depth t:ℝ)-2*(depth t:ℝ)^2*δ-
      countPenalty C (depth t) (jointError (depth t) δ K)≤Real.logb 2 d := by
    nlinarith only [hfinite,hf]
  have hv : 3+thetaK-γ ≤
      ((3+thetaK-ω δ)*(depth t:ℝ)-2*(depth t:ℝ)^2*δ-
        countPenalty C (depth t) (jointError (depth t) δ K))/t := by
    simpa only [hδeq,sub_div,mul_div_assoc] using hvalue
  exact ((le_div_iff₀ ht).mp hv).trans hbound

end
end E2

