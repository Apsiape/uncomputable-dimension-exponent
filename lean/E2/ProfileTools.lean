import E2.Lower
import E2.Finite
import Mathlib.Topology.Algebra.Order.Floor

namespace E2.ProfileTools
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter

variable {ι : Type*} {P : Presentation ι} {flat : Bool} {δ : ℝ}

theorem dimension_finite (d : ℕ) (m : Model P d δ) (hm : flat = true → m.Flat) :
    modelDimension P flat δ ≠ ⊤ := by
  classical
  have he : ∃ d, ∃ m : Model P d δ, flat = true → m.Flat := ⟨d,m,hm⟩
  simp only [modelDimension,dif_pos he]
  exact ENat.coe_ne_top _

theorem dimension_le (d : ℕ) (m : Model P d δ) (hm : flat = true → m.Flat) :
    (modelDimension P flat δ).toNat ≤ d := by
  classical
  have he : ∃ d, ∃ m : Model P d δ, flat = true → m.Flat := ⟨d,m,hm⟩
  simp only [modelDimension,dif_pos he,ENat.toNat_coe]
  exact Nat.find_min' he ⟨m,hm⟩

theorem dimension_model (h : modelDimension P flat δ ≠ ⊤) :
    ∃ m : Model P (modelDimension P flat δ).toNat δ, flat = true → m.Flat := by
  classical
  have he : ∃ d, ∃ m : Model P d δ, flat = true → m.Flat := by
    by_contra hn
    exact h (by simp only [modelDimension,dif_neg hn])
  have hv : modelDimension P flat δ = (Nat.find he : ℕ∞) := by
    exact dif_pos he
  have hn : (modelDimension P flat δ).toNat = Nat.find he := by rw [hv]; rfl
  rw [hn]
  exact Nat.find_spec he

def depth (t : ℝ) : ℕ := 2 * (⌈(t + Real.logb 4 3)/2⌉₊ + 1)

theorem depth_ge_two (t : ℝ) : 2 ≤ depth t := by unfold depth; omega
 theorem depth_even (t : ℝ) : Even (depth t) := ⟨⌈(t + Real.logb 4 3)/2⌉₊ + 1,by unfold depth; omega⟩

theorem depth_lower (t : ℝ) : t + Real.logb 4 3 ≤ (depth t : ℝ) := by
  classical
  have h := Nat.le_ceil ((t + Real.logb 4 3)/2)
  simp only [depth,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  linarith

theorem depth_upper (t : ℝ) (ht : 0 ≤ t) :
    (depth t : ℝ) ≤ t + Real.logb 4 3 + 4 := by
  have hl : 0 ≤ Real.logb 4 3 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (t + Real.logb 4 3)/2)
  simp only [depth,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  linarith

theorem depth_atTop : Tendsto depth atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop ((n:ℝ)-Real.logb 4 3)] with t ht
  have hn : (n:ℝ) ≤ (depth t:ℝ) := by linarith [depth_lower t]
  exact_mod_cast hn

theorem depth_ratio : Tendsto (fun t : ℝ => (depth t:ℝ)/t) atTop (nhds 1) := by
  classical
  have lo : Tendsto (fun t : ℝ => 1 + Real.logb 4 3 / t) atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_inv_atTop_zero.const_mul (Real.logb 4 3))
  have hi : Tendsto (fun t : ℝ => 1 + (Real.logb 4 3+4) / t) atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_inv_atTop_zero.const_mul (Real.logb 4 3+4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [← div_self ht.ne',← add_div]
    exact div_le_div_of_nonneg_right (depth_lower t) ht.le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [← div_self ht.ne',← add_div]
    exact div_le_div_of_nonneg_right (by linarith [depth_upper t ht.le]) ht.le

theorem log_depth_ratio : Tendsto (fun t : ℝ => Real.logb 2 ((depth t:ℝ)+2)/t)
    atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.logb 2 x / (x-2)) atTop (nhds 0) := by
    simpa [sub_eq_add_neg] using (Real.tendsto_pow_logb_div_mul_add_atTop (b := (2:ℝ)) 1 (-2) 1 one_ne_zero)
  have hd : Tendsto (fun t : ℝ => (depth t:ℝ)+2) atTop atTop :=
    tendsto_atTop.2 (fun x => by
      filter_upwards [(tendsto_natCast_atTop_atTop.comp depth_atTop).eventually
        (eventually_ge_atTop x)] with t ht
      dsimp only [Function.comp_def] at ht
      linarith)
  have hm := (hlog.comp hd).mul depth_ratio
  convert hm using 1
  · ext t
    simp only [Function.comp_def,add_sub_cancel_right]
    have hn : (depth t:ℝ) ≠ 0 := by exact_mod_cast (by have := depth_ge_two t; omega : depth t ≠ 0)
    field_simp
  · simp

theorem precision_le (t : ℝ) : 3*(4:ℝ)^(-(depth t:ℤ)) ≤ (4:ℝ)^(-t) := by
  classical
  have hz : (4:ℝ)^(-(depth t:ℤ)) = (4:ℝ)^(-(depth t:ℝ)) := by
    rw [← Real.rpow_intCast]
    simp
  rw [hz]
  calc
    _ = (4:ℝ)^(Real.logb 4 3 - (depth t:ℝ)) := by
      rw [Real.rpow_sub (by norm_num),Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
        Real.rpow_neg (by norm_num)]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [depth_lower t])

end
end E2.ProfileTools
