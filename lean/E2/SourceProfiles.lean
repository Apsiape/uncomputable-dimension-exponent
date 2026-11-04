import E2.ProfileTools

namespace E2.ProfileTools
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

/-- The finite-model input with its original flatness and operator-norm clauses. -/
def FiniteEstimates (p : CounterProgram) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → Even N →
    ∃ k : ℕ, |(k:ℝ)-thetaN p N*N| ≤ C*Real.logb 2 (N+2) ∧
      ∃ m : Model (sourcePresentation p) (2^(3*N+k)) (3*(4:ℝ)^(-(N:ℤ))),
        m.Flat ∧ ∀ r ∈ (sourcePresentation p).relations,
          ‖Poly.eval m.value r‖ ≤ 3*(4:ℝ)^(-(N:ℤ))

theorem upper_models (p : CounterProgram) (hf : FiniteEstimates p) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∃ d : ℕ,
      ∃ m : Model (sourcePresentation p) d ((4:ℝ)^(-t)), m.Flat ∧
        Real.logb 2 d ≤ (3 + thetaN p (depth t)) * (depth t:ℝ) +
          C * Real.logb 2 ((depth t:ℝ)+2) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C,hC,?_⟩
  intro t
  obtain ⟨k,hk,m,hm,hr⟩ := hf (depth t) (depth_ge_two t) (depth_even t)
  refine ⟨2^(3*depth t+k),m.weaken (precision_le t),hm,?_⟩
  have hl : Real.logb 2 ((2^(3*depth t+k):ℕ):ℝ) = 3*(depth t:ℝ)+(k:ℝ) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow]
    norm_num
  rw [hl]
  have hh := (abs_le.mp hk).2
  nlinarith

theorem precision_log (t : ℝ) : Real.logb 4 (1 / ((4:ℝ)^(-t))) = t := by
  rw [one_div,Real.logb_inv,Real.logb_rpow (by norm_num) (by norm_num)]
  ring

theorem precision_inverse {δ : ℝ} (hδ : 0 < δ) :
    (4:ℝ)^(-Real.logb 4 (1/δ)) = δ := by
  rw [one_div,Real.logb_inv,neg_neg,Real.rpow_logb (by norm_num) (by norm_num) hδ]

theorem inverse_log_atTop : Tendsto (fun δ : ℝ => Real.logb 4 (1/δ))
    (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  simpa only [one_div,Real.logb_inv,Function.comp_def] using
    tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1:ℝ)<4))

theorem source_profile (p : CounterProgram)
    (hlower : UniformLower (sourcePresentation p) (3+thetaK))
    (hf : FiniteEstimates p)
    (hlimit : Tendsto (thetaN p) atTop (nhds thetaK)) (flat : Bool) :
    (∀ δ, 0 < δ → modelDimension (sourcePresentation p) flat δ ≠ ⊤) ∧
      Tendsto (fun δ => Real.logb 2 ((modelDimension (sourcePresentation p) flat δ).toNat:ℝ) /
        Real.logb 4 (1/δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (3+thetaK)) := by
  classical
  obtain ⟨C,hC,hmodels⟩ := upper_models p hf
  let D := modelDimension (sourcePresentation p) flat
  have hfinite (t : ℝ) : D ((4:ℝ)^(-t)) ≠ ⊤ := by
    obtain ⟨d,m,hm,hbound⟩ := hmodels t
    exact dimension_finite d m (fun _ => hm)
  have hfinite_all (δ : ℝ) (hδ : 0 < δ) : D δ ≠ ⊤ := by
    simpa only [precision_inverse hδ] using hfinite (Real.logb 4 (1/δ))
  refine ⟨hfinite_all,?_⟩
  let f := fun t : ℝ => Real.logb 2 ((D ((4:ℝ)^(-t))).toNat:ℝ) / t
  let u := fun t : ℝ => (3+thetaN p (depth t))*((depth t:ℝ)/t) +
    C*(Real.logb 2 ((depth t:ℝ)+2)/t)
  have hu : Tendsto u atTop (nhds (3+thetaK)) := by
    simpa only [u,Function.comp_def,mul_one,mul_zero,add_zero] using
      (((tendsto_const_nhds (x := (3:ℝ))).add (hlimit.comp depth_atTop)).mul depth_ratio).add
        (log_depth_ratio.const_mul C)
  have hupper : ∀ᶠ t : ℝ in atTop, f t ≤ u t := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    obtain ⟨d,m,hm,hbound⟩ := hmodels t
    obtain ⟨mmin,hmin⟩ := dimension_model (hfinite t)
    have hpos : (0:ℝ) < ((D ((4:ℝ)^(-t))).toNat:ℝ) := by
      exact_mod_cast mmin.positive_dimension
    have hd : ((D ((4:ℝ)^(-t))).toNat:ℝ) ≤ (d:ℝ) := by
      exact_mod_cast dimension_le d m (fun _ => hm)
    have hlog := (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hpos hd).trans hbound
    have hh := div_le_div_of_nonneg_right hlog ht.le
    simpa only [f,u,add_div,mul_div_assoc] using hh
  have hlower_event (γ : ℝ) (hγ : 0 < γ) : ∀ᶠ t : ℝ in atTop, 3+thetaK-γ ≤ f t := by
    obtain ⟨δ₀,hδ₀,hlow⟩ := hlower γ hγ
    filter_upwards [eventually_gt_atTop (0:ℝ),
      (real_precision_tendsto.mono_right inf_le_left).eventually (Iio_mem_nhds hδ₀)] with t ht hsmall
    obtain ⟨mmin,hmin⟩ := dimension_model (hfinite t)
    have h := hlow ((4:ℝ)^(-t)) _ mmin (by positivity) hsmall
    rw [precision_log] at h
    exact (le_div_iff₀ ht).mpr h
  have hflim : Tendsto f atTop (nhds (3+thetaK)) := by
    apply tendsto_order.2
    constructor
    · intro x hx
      filter_upwards [hlower_event ((3+thetaK-x)/2) (by linarith)] with t ht
      linarith
    · intro x hx
      filter_upwards [hupper,hu.eventually (Iio_mem_nhds hx)] with t ht hu
      exact ht.trans_lt hu
  have hcomp := hflim.comp inverse_log_atTop
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  dsimp only [Function.comp_def,f]
  rw [precision_inverse hδ]

end
end E2.ProfileTools
