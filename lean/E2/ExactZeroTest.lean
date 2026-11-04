import E2.Clock
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

namespace E2.ExactForcing
noncomputable section
variable {A : Type*} [CStarAlgebra A]

 theorem contraction_norm (s : A) (hs : IsSelfAdjoint s)
    (hσ : spectrum ℝ s ⊆ Set.Icc 0 1) : ‖s‖ ≤ 1 := by
  have h : ‖cfc (fun x : ℝ => x) s‖ ≤ 1 := norm_cfc_le (by norm_num)
    (fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hσ hx).1] using (hσ hx).2)
  simpa only [cfc_id' ℝ s hs] using h

/-- Exact right-action zero test. Positive encoded powers below one are
separated algebraically; the zero counter uses a strict contraction. -/
 theorem zero_test (r z s q : A) (hzz : z*z=z) (hcomm : z*s=s*z)
    (hsnorm : ‖s‖≤1) (heq : r=z+(1/2:ℂ) • ((1-z)*s))
    (n : ℕ) (hencoded : r*q=((2:ℂ)^(-(n:ℤ))) • q) :
    z*q = if n=0 then q else 0 := by
  have hzr : z*r=z := by
    rw [heq, mul_add, mul_smul_comm, ←mul_assoc, mul_sub, mul_one, hzz,
      sub_self, zero_mul, smul_zero, add_zero]
  have hzencoded : z*q = ((2:ℂ)^(-(n:ℤ))) • (z*q) := by
    calc
      _ = (z*r)*q := by rw [hzr]
      _ = _ := by rw [mul_assoc, hencoded, mul_smul_comm]
  by_cases hn : n=0
  · subst n
    simp only [Int.natCast_zero, neg_zero, zpow_zero, one_smul] at hencoded
    simp only [ite_true]
    let w := (1-z)*q
    have hw : w=(1/2:ℂ) • (s*w) := by
      have he := congrArg (fun a : A => (1-z)*a) hencoded
      rw [heq, add_mul, smul_mul_assoc, mul_add, mul_smul_comm] at he
      have h1 : (1-z)*z=0 := by rw [sub_mul, one_mul, hzz, sub_self]
      have h2 : (1-z)*(1-z)=1-z := by noncomm_ring [hzz]
      have h3 : (1-z)*s=s*(1-z) := by rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
      rw [←mul_assoc (1-z) z q, h1, zero_mul, zero_add] at he
      have ht : (1-z)*((1-z)*s*q)=s*((1-z)*q) := by
        calc
          _ = ((1-z)*(1-z))*s*q := by noncomm_ring
          _ = (1-z)*s*q := by rw [h2]
          _ = _ := by rw [h3, mul_assoc]
      rw [ht] at he
      exact he.symm
    have hnorm : ‖w‖≤(1/2:ℝ)*‖w‖ := by
      calc
        _ = ‖(1/2:ℂ) • (s*w)‖ := congrArg norm hw
        _ = (1/2:ℝ)*‖s*w‖ := by rw [norm_smul]; norm_num
        _ ≤ (1/2:ℝ)*(‖s‖*‖w‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by norm_num)
        _ ≤ (1/2:ℝ)*‖w‖ := by nlinarith [norm_nonneg w]
    have hwzero : w=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w])
    have he : q-z*q=0 := by simpa only [w, sub_mul, one_mul] using hwzero
    exact (sub_eq_zero.mp he).symm
  · simp only [hn, ite_false]
    have hl : (2:ℂ)^(-(n:ℤ)) ≠ 1 := by
      rw [zpow_neg]
      have hn' : 0<n := Nat.pos_of_ne_zero hn
      have hreal : (1:ℝ)<2^n := one_lt_pow₀ (by norm_num) (by omega)
      intro h
      have hc : (2:ℂ)^n=1 := by simpa using congrArg (fun z : ℂ => z⁻¹) h
      have hr : (2:ℝ)^n=1 := by exact_mod_cast hc
      exact (ne_of_gt hreal) hr
    have he : (1-(2:ℂ)^(-(n:ℤ))) • (z*q)=0 := by
      rw [sub_smul, one_smul, ←hzencoded, sub_self]
    exact (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (Ne.symm hl))

end
end E2.ExactForcing



