import E2.ExactClockTrace

namespace E2.ExactTrace
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem cfc_nonneg (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hf0 : ∀ x∈spectrum ℝ a, 0≤f x) : 0≤(τ.toLinearMap (cfc f a)).re := by
  let g : ℝ → ℝ := fun x => Real.sqrt (f x)
  have hg : ContinuousOn g (spectrum ℝ a) := Real.continuous_sqrt.comp_continuousOn hf
  have he : star (cfc g a)*cfc g a=cfc f a := by
    rw [(IsSelfAdjoint.cfc (f:=g) (a:=a)).star_eq,←cfc_mul g g a hg hg]
    apply cfc_congr
    intro x hx
    exact Real.mul_self_sqrt (hf0 x hx)
  rw [←he]
  exact τ.positive _

theorem cfc_mono (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ a))
    (hg : ContinuousOn g (spectrum ℝ a)) (hfg : ∀ x∈spectrum ℝ a, f x≤g x) :
    (τ.toLinearMap (cfc f a)).re≤(τ.toLinearMap (cfc g a)).re := by
  have h := cfc_nonneg τ a ha (fun x => g x-f x) (hg.sub hf) (fun x hx => sub_nonneg.mpr (hfg x hx))
  rw [cfc_sub g f a hg hf,map_sub,Complex.sub_re] at h
  linarith

theorem cfc_const (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a) (r : ℝ) :
    (τ.toLinearMap (cfc (fun _ : ℝ => r) a)).re=r := by
  rw [_root_.cfc_const r a ha,Algebra.algebraMap_eq_smul_one,ExactClock.real_smul,
    map_smul,τ.normalized]
  simp

/-- Vanishing real moments kill every real mass at the top eigenspace. -/
theorem top_projection_real (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (hσ : spectrum ℝ a ⊆ Set.Icc 0 1)
    (hmom : Filter.Tendsto (fun n : ℕ => (τ.toLinearMap (a^n)).re) Filter.atTop (nhds 0))
    (e : A) (he : star e=e) (hee : e*e=e) (hae : a*e=e) :
    (τ.toLinearMap e).re=0 := by
  have hnonneg : 0≤(τ.toLinearMap e).re := by
    simpa only [he,hee] using τ.positive e
  apply le_antisymm ?_ hnonneg
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hmom
  apply Filter.Eventually.of_forall
  intro n
  let f : ℝ → ℝ := fun x => Real.sqrt (x^n)
  let q := cfc f a
  have hf : Continuous f := by unfold f; fun_prop
  have hq : star q=q := (IsSelfAdjoint.cfc (f:=f) (a:=a)).star_eq
  have hqe : q*e=e := by
    have h := ExactClock.intertwines a 1 e ha (IsSelfAdjoint.one A)
      (by simpa only [mul_one] using hae) f hf
    simpa only [q,cfc_apply_one,f,one_pow,Real.sqrt_one,map_one,mul_one] using h
  have heq : e*q=e := by
    have h := congrArg star hqe
    simpa only [star_mul,hq,he] using h
  have hsq : q*q=a^n := by
    change cfc f a*cfc f a=a^n
    rw [←cfc_mul f f a hf.continuousOn hf.continuousOn,←cfc_pow_id (R:=ℝ) a n ha]
    apply cfc_congr
    intro x hx
    have hx0 : 0≤x^n := pow_nonneg (hσ hx).1 n
    exact Real.mul_self_sqrt hx0
  have hcomp : star (q*(1-e))*(q*(1-e))=a^n-e := by
    simp only [star_mul,star_sub,star_one,he,hq]
    noncomm_ring [hsq,hqe,heq,hee]
  have h := τ.positive (q*(1-e))
  rw [hcomp,map_sub,Complex.sub_re] at h
  linarith
end
end E2.ExactTrace



