import E2.EffectiveCoding
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace E2.RationalLogarithm
open EffectiveCoding Primrec

theorem nat_pow : Primrec₂ (fun m n : ℕ => m^n) := Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem nat_log_two : Primrec (Nat.log 2) := by
  have hp : PrimrecRel (fun m j : ℕ => 2^j ≤ m) :=
    nat_le.comp (nat_pow.comp (const 2) snd) fst
  refine (nat_findGreatest .id hp).of_eq ?_
  intro m
  by_cases hm : m=0
  · simp [hm]
  · apply le_antisymm
    · exact Nat.le_log_of_pow_le (by norm_num)
        (Nat.findGreatest_spec (P := fun j => 2^j ≤ m) (Nat.zero_le m) (by simpa using Nat.one_le_iff_ne_zero.mpr hm))
    · exact Nat.le_findGreatest (Nat.log_le_self 2 m) (Nat.pow_log_le_self 2 hm)

def approx (m k : ℕ) : ℚ := (Nat.log 2 (m^(2^(k+1))) : ℚ) / (2^(k+1) : ℕ)

theorem approx_computable : Computable (fun p : ℕ × ℕ => approx p.1 p.2) := by
  have ht : Primrec (fun p : ℕ × ℕ => 2^(p.2+1)) := nat_pow.comp (const 2) (succ.comp snd)
  have hj : Primrec (fun p : ℕ × ℕ => Nat.log 2 (p.1^(2^(p.2+1)))) :=
    nat_log_two.comp (nat_pow.comp fst ht)
  exact (rat_divNat.comp ((int_ofNat.comp hj).to_comp.pair ht.to_comp)).of_eq (fun _ => rfl)

/-- An integer-power calculation gives a rational binary-logarithm approximation;
no algorithm on real inputs, nor analytic logarithm routine, is assumed. -/
theorem approx_error (m k : ℕ) (_hm : 0 < m) :
    |(approx m k : ℝ)-Real.logb 2 (m : ℝ)| ≤ (2:ℝ)^(-(k+1:ℤ)) := by
  let t : ℕ := 2^(k+1)
  let x : ℝ := Real.logb 2 (m : ℝ)
  let j : ℕ := Nat.log 2 (m^t)
  have ht : (0:ℝ) < t := by dsimp [t]; positivity
  have hlow : (j:ℝ) ≤ (t:ℝ)*x := by
    have h := Real.natLog_le_logb (m^t) 2
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,j,x] using h
  have hupp : (t:ℝ)*x < (j:ℝ)+1 := by
    have h := Nat.lt_floor_add_one (Real.logb 2 ((m^t:ℕ):ℝ))
    have hf : ⌊Real.logb 2 ((m^t:ℕ):ℝ)⌋₊ = Nat.log 2 (m^t) := by
      simpa using Real.natFloor_logb_natCast 2 (m^t)
    rw [hf] at h
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,j,x] using h
  have he : (approx m k : ℝ) = (j:ℝ)/(t:ℝ) := by
    simp [approx,j,t]
  rw [he,abs_of_nonpos (sub_nonpos.mpr ((div_le_iff₀ ht).mpr (by simpa [mul_comm] using hlow)))]
  have hb : x-(j:ℝ)/(t:ℝ) ≤ 1/(t:ℝ) := by
    apply (le_div_iff₀ ht).mpr
    field_simp
    nlinarith
  have htEq : 1/(t:ℝ) = (2:ℝ)^(-(k+1:ℤ)) := by
    simp only [t,Nat.cast_pow,Nat.cast_ofNat]
    rw [show -(k+1:ℤ) = -((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,one_div]
  linarith [hb,htEq]

end E2.RationalLogarithm
