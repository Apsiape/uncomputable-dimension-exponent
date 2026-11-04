import E2.SourceCross

namespace E2
noncomputable section

theorem rawClockScale_mono (A B δ : ℝ) (M : ℕ) (hδ : 0 ≤ δ) (hAB : A ≤ B) :
    rawClockScale A M δ ≤ rawClockScale B M δ := by unfold rawClockScale; gcongr

theorem joint_word_scale (K δ : ℝ) (M i j : ℕ) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hi : i ≤ M) (hj : j ≤ M) :
    5*(2*(i:ℝ)+1)*(2*(j:ℝ)+1)*(2*i+2*j+3)*δ ≤ 80*rawClockScale K M δ := by
  have hir : (i:ℝ) ≤ M := by exact_mod_cast hi
  have hjr : (j:ℝ) ≤ M := by exact_mod_cast hj
  have hM : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : 2*(i:ℝ)+1 ≤ 2*((M:ℝ)+1) := by linarith
  have h2 : 2*(j:ℝ)+1 ≤ 2*((M:ℝ)+1) := by linarith
  have h3 : 2*(i:ℝ)+2*j+3 ≤ 4*((M:ℝ)+1) := by linarith
  have hc : 5*(2*(i:ℝ)+1)*(2*(j:ℝ)+1)*(2*i+2*j+3) ≤ 80*((M:ℝ)+1)^3 := by
    calc
      _ ≤ 5*(2*((M:ℝ)+1))*(2*((M:ℝ)+1))*(4*((M:ℝ)+1)) := by gcongr
      _ = _ := by ring
  have hfour : (1:ℝ) ≤ 4^M := one_le_pow₀ (by norm_num)
  have hb : ((M:ℝ)+1)^3*δ ≤ rawClockScale K M δ := by
    unfold rawClockScale
    calc
      _ = 1*((M:ℝ)+1)^3*1*δ := by ring
      _ ≤ _ := by gcongr
  nlinarith [mul_le_mul_of_nonneg_right hc hδ]

theorem joint_address_scale (A K δ : ℝ) (M i j : ℕ) (hA : 0 ≤ A) (hAK : A ≤ K)
    (hK : 1 ≤ K) (hδ : 0 ≤ δ) (hi : i ≤ M) (hj : j ≤ M) :
    A*((i:ℝ)+1)*4^j*δ ≤ rawClockScale K M δ := by
  have hir : (i:ℝ) ≤ M := by exact_mod_cast hi
  have hp : (M:ℝ)+1 ≤ ((M:ℝ)+1)^3 := by
    simpa using pow_le_pow_right₀ (show (1:ℝ) ≤ (M:ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) M; linarith) (show 1 ≤ 3 by decide)
  have hpow : (4:ℝ)^j ≤ 4^M := pow_le_pow_right₀ (by norm_num) hj
  unfold rawClockScale
  gcongr
  linarith

end
end E2
