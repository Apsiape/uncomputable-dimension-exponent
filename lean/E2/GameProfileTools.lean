import E2.SourceProfiles
import E2.BooleanGameLoss

namespace E2.ProfileTools
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
variable {G : BCSGame}

theorem game_dimension_finite {ε : ℝ} {d : ℕ} (s : Strategy G d) (hd : 0 < d) (hs : loss s ≤ ε) :
    dimension G ε ≠ ⊤ := by
  classical
  have he : ∃ d, Feasible G ε d := ⟨d,hd,s,hs⟩
  simp only [dimension,dif_pos he]
  exact ENat.natCast_ne_top _

theorem game_dimension_le {ε : ℝ} {d : ℕ} (s : Strategy G d) (hd : 0 < d) (hs : loss s ≤ ε) :
    (dimension G ε).toNat ≤ d := by
  classical
  have he : ∃ d, Feasible G ε d := ⟨d,hd,s,hs⟩
  simp only [dimension,dif_pos he,ENat.toNat_natCast]
  exact Nat.find_min' he ⟨hd,s,hs⟩

theorem game_dimension_strategy {ε : ℝ} (h : dimension G ε ≠ ⊤) :
    Feasible G ε (dimension G ε).toNat := by
  classical
  have he : ∃ d, Feasible G ε d := by
    by_contra hn
    exact h (by simp only [dimension,dif_neg hn])
  have hv : dimension G ε = (Nat.find he : ℕ∞) := dif_pos he
  rw [hv,ENat.toNat_natCast]
  exact Nat.find_spec he

def scale (k t : ℝ) := k * (4:ℝ)^(-(t/2))

theorem scale_pos {k : ℝ} (hk : 0 < k) (t : ℝ) : 0 < scale k t := by
  unfold scale
  positivity

theorem scale_log {k : ℝ} (hk : 0 < k) (t : ℝ) :
    Real.logb 4 (1/scale k t) = t/2 - Real.logb 4 k := by
  rw [one_div,Real.logb_inv,scale,Real.logb_mul hk.ne'
    (ne_of_gt (by positivity : 0 < (4:ℝ)^(-(t/2)))),
    Real.logb_rpow (by norm_num) (by norm_num)]
  ring

theorem scale_limit {k : ℝ} (hk : 0 < k) : Tendsto (scale k) atTop
    (nhdsWithin 0 (Set.Ioi 0)) := by
  have ht : Tendsto (fun t : ℝ => t/2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Tendsto (fun t : ℝ => k * (4:ℝ)^(-(t/2))) atTop (nhds 0)
    simpa only [mul_zero,Function.comp_def] using
      ((real_precision_tendsto.mono_right inf_le_left).comp ht).const_mul k
  · exact Eventually.of_forall (scale_pos hk)

theorem scale_log_ratio {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.logb 4 (1/scale k t)/t) atTop (nhds (1/2)) := by
  have h := (tendsto_const_nhds (x := (1/2:ℝ))).sub
    (tendsto_inv_atTop_zero.const_mul (Real.logb 4 k))
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [scale_log hk]
  field_simp

theorem scaled_profile (D : ℝ → ℕ∞) (s : ℝ)
    (h : Tendsto (fun δ => Real.logb 2 ((D δ).toNat:ℝ) / Real.logb 4 (1/δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds s)) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => Real.logb 2 ((D (scale k t)).toNat:ℝ) / t)
      atTop (nhds (s/2)) := by
  have hm := (h.comp (scale_limit hk)).mul (scale_log_ratio hk)
  have he : ∀ᶠ t : ℝ in atTop, Real.logb 4 (1/scale k t) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (2*Real.logb 4 k)] with t ht
    rw [scale_log hk]
    linarith
  have hv : s * (1/2) = s/2 := by ring
  rw [hv] at hm
  apply hm.congr'
  filter_upwards [he] with t ht
  dsimp only [Function.comp_def]
  field_simp

theorem sqrt_precision (t : ℝ) : Real.sqrt ((4:ℝ)^(-t)) = (4:ℝ)^(-(t/2)) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  ring

theorem scale_completeness {C : ℝ} (hC : 0 < C) (t : ℝ) :
    C * (scale (1/Real.sqrt C) t)^2 = (4:ℝ)^(-t) := by
  rw [scale,mul_pow,one_div_pow,Real.sq_sqrt hC.le,← sqrt_precision,Real.sq_sqrt (by positivity)]
  field_simp

theorem theta_nonneg : 0 ≤ thetaK := by
  classical
  unfold thetaK
  apply tsum_nonneg
  intro e
  split_ifs <;> simp [haltingWeight] <;> positivity

theorem no_zero_model {ι : Type*} (P : Presentation ι)
    (hlower : UniformLower P (3+thetaK)) {d : ℕ} (m : Model P d 0) : False := by
  obtain ⟨δ₀,hδ₀,hlow⟩ := hlower 1 (by norm_num)
  have ha : 0 < 2+thetaK := by linarith [theta_nonneg]
  have he : ∀ᶠ t : ℝ in atTop,
      (4:ℝ)^(-t) < δ₀ ∧ Real.logb 2 d < (2+thetaK)*t := by
    filter_upwards [(real_precision_tendsto.mono_right inf_le_left).eventually (Iio_mem_nhds hδ₀),
      eventually_gt_atTop (Real.logb 2 d/(2+thetaK))] with t hδ ht
    exact ⟨hδ,by simpa only [mul_comm] using (div_lt_iff₀ ha).mp ht⟩
  obtain ⟨t,hsmall,hbig⟩ := he.exists
  have h := hlow ((4:ℝ)^(-t)) d (m.weaken (by positivity)) (by positivity) hsmall
  rw [precision_log] at h
  linarith

end
end E2.ProfileTools
