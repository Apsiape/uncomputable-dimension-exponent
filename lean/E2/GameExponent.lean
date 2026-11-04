import E2.GameProfileTools

namespace E2.ProfileTools
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

 theorem log_nat_bound {n c d : ℕ} (hn : 0 < n) (hc : 0 < c) (hd : 0 < d)
    (h : n ≤ c*d) : Real.logb 2 n ≤ Real.logb 2 c + Real.logb 2 d := by
  have hp : (0:ℝ) < n := by exact_mod_cast hn
  have hh : (n:ℝ) ≤ (c:ℝ)*(d:ℝ) := by exact_mod_cast h
  have hc0 : (c:ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [Real.logb_mul hc0 hd0] using
    Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hp hh

theorem game_conclusions {ι : Type*} (P : Presentation ι) (G : BCSGame)
    (c : ℕ) (hc : 0 < c) (C : ℝ) (hC : 0 < C)
    (sound : ∀ (ε : ℝ) (d : ℕ) (s : Strategy G d), 0 ≤ ε → loss s ≤ ε →
      ∃ d', d' ≤ c*d ∧ Nonempty (Model P d' (C*Real.sqrt ε)))
    (complete : ∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0 ≤ δ → m.Flat →
      ∃ d', 0 < d' ∧ d' ≤ c*d ∧ ∃ s : Strategy G d', loss s ≤ C*δ^2)
    (hWfinite : ∀ δ, 0 < δ → W P δ ≠ ⊤)
    (hWslope : Tendsto (fun δ => Real.logb 2 ((W P δ).toNat:ℝ) / Real.logb 4 (1/δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3+thetaK)))
    (hHfinite : ∀ δ, 0 < δ → H P δ ≠ ⊤)
    (hHslope : Tendsto (fun δ => Real.logb 2 ((H P δ).toNat:ℝ) / Real.logb 4 (1/δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3+thetaK)))
    (hlower : UniformLower P (3+thetaK)) :
    quantumValue G = 1 ∧ NoPerfectStrategy G ∧ DimensionExponent G betaK := by
  classical
  have hexists (ε : ℝ) (hε : 0 < ε) : ∃ d, 0 < d ∧ ∃ s : Strategy G d, loss s ≤ ε := by
    let δ := Real.sqrt (ε/C)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hε hC)
    obtain ⟨m,hm⟩ := dimension_model (hHfinite δ hδ)
    obtain ⟨d,hd,hbound,s,hs⟩ := complete δ _ m hδ.le (hm rfl)
    refine ⟨d,hd,s,?_⟩
    have he : C*δ^2 = ε := by
      dsimp only [δ]
      rw [Real.sq_sqrt (le_of_lt (div_pos hε hC))]
      field_simp
    exact hs.trans he.le
  have hfinite (ε : ℝ) (hε : 0 < ε) : dimension G ε ≠ ⊤ := by
    obtain ⟨d,hd,s,hs⟩ := hexists ε hε
    exact game_dimension_finite s hd hs
  have hvalue : quantumValue G = 1 := by
    let S := {w : ℝ | ∃ d : ℕ, 0 < d ∧ ∃ s : Strategy G d, winningProbability s = w}
    have hbounded : ∀ w ∈ S, w ≤ 1 := by
      rintro w ⟨d,hd,s,rfl⟩
      have hh := BooleanGameLoss.loss_eq_sum s
      have hn : 0 ≤ loss s := by
        rw [hh]
        apply Finset.sum_nonneg
        intro c hc
        apply Finset.sum_nonneg
        intro v hv
        exact mul_nonneg (by exact_mod_cast G.probability_nonneg c v)
          (BooleanGameLoss.localLoss_nonneg s c v)
      exact sub_nonneg.mp hn
    have hbdd : BddAbove S := ⟨1,hbounded⟩
    have hne : S.Nonempty := by
      obtain ⟨d,hd,s,hs⟩ := hexists 1 (by norm_num)
      exact ⟨winningProbability s,d,hd,s,rfl⟩
    change sSup S = 1
    apply le_antisymm (csSup_le hne hbounded)
    by_contra hn
    have hq : sSup S < 1 := lt_of_not_ge hn
    obtain ⟨d,hd,s,hs⟩ := hexists ((1-sSup S)/2) (by linarith)
    have hw : winningProbability s ≤ sSup S := le_csSup hbdd ⟨d,hd,s,rfl⟩
    unfold loss at hs
    linarith
  have hperfect : NoPerfectStrategy G := by
    intro d hd s hs
    obtain ⟨d',hd',⟨m⟩⟩ := sound 0 d s le_rfl hs.le
    have m0 : Model P d' 0 := by simpa only [Real.sqrt_zero,mul_zero] using m
    exact no_zero_model P hlower m0
  have hlo (t : ℝ) :
      Real.logb 2 ((W P (scale C t)).toNat:ℝ) - Real.logb 2 c ≤
        logDimension G ((4:ℝ)^(-t)) := by
    obtain ⟨hd,s,hs⟩ := game_dimension_strategy (hfinite ((4:ℝ)^(-t)) (by positivity))
    obtain ⟨d',hd',⟨m⟩⟩ := sound _ _ s (by positivity) hs
    have m' : Model P d' (scale C t) := by simpa only [scale,sqrt_precision] using m
    obtain ⟨mw,hmw⟩ := dimension_model (hWfinite (scale C t) (scale_pos hC t))
    have hn : (W P (scale C t)).toNat ≤ c*(dimension G ((4:ℝ)^(-t))).toNat :=
      (dimension_le d' m' (by simp)).trans hd'
    have hh := log_nat_bound mw.positive_dimension hc hd hn
    change Real.logb 2 ((W P (scale C t)).toNat:ℝ) ≤
      Real.logb 2 c + Real.logb 2 ((dimension G ((4:ℝ)^(-t))).toNat:ℝ) at hh
    change _ ≤ Real.logb 2 ((dimension G ((4:ℝ)^(-t))).toNat:ℝ)
    linarith
  have hhi (t : ℝ) : logDimension G ((4:ℝ)^(-t)) ≤
      Real.logb 2 c + Real.logb 2 ((H P (scale (1/Real.sqrt C) t)).toNat:ℝ) := by
    have hk : 0 < 1/Real.sqrt C := by positivity
    obtain ⟨m,hm⟩ := dimension_model (hHfinite _ (scale_pos hk t))
    obtain ⟨d,hd,hbound,s,hs⟩ := complete _ _ m (scale_pos hk t).le (hm rfl)
    rw [scale_completeness hC] at hs
    have hn := (game_dimension_le s hd hs).trans hbound
    have hmin := (game_dimension_strategy (hfinite ((4:ℝ)^(-t)) (by positivity))).1
    exact log_nat_bound hmin hc m.positive_dimension hn
  have hconst : Tendsto (fun t : ℝ => Real.logb 2 c/t) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (Real.logb 2 c)
  have hlowlim := (scaled_profile (W P) _ hWslope hC).sub hconst
  have hhilim := hconst.add (scaled_profile (H P) _ hHslope (by positivity : 0 < 1/Real.sqrt C))
  have hgame : Tendsto (fun t : ℝ => logDimension G ((4:ℝ)^(-t))/t)
      atTop (nhds ((3+thetaK)/2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlowlim) (by simpa using hhilim)
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      simpa only [sub_div] using div_le_div_of_nonneg_right (hlo t) ht.le
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      simpa only [add_div,one_div] using div_le_div_of_nonneg_right (hhi t) ht.le
  refine ⟨hvalue,hperfect,hfinite,?_⟩
  have hhalf := (hgame.div_const 2).comp inverse_log_atTop
  have hb : ((3+thetaK)/2)/2 = betaK := by unfold betaK; ring
  rw [hb] at hhalf
  apply hhalf.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  dsimp only [Function.comp_def]
  rw [precision_inverse hε]
  have hlog : Real.logb 2 (1/ε) = 2 * Real.logb 4 (1/ε) := by
    rw [Real.logb,Real.logb]
    have hh : Real.log (4:ℝ) = 2*Real.log 2 := by
      have h := Real.log_pow (2:ℝ) 2
      norm_num at h
      exact h
    rw [hh]
    field_simp
    <;> ring
  rw [hlog]
  ring

end
end E2.ProfileTools
