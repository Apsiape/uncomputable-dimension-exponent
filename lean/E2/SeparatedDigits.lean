import E2.EffectiveCoding
import Mathlib.Analysis.SpecificLimits.Basic

namespace E2.SeparatedDigits
noncomputable section
open scoped BigOperators
open Encodable EffectiveCoding
attribute [local instance] Classical.propDecidable

def bit (A : Set ℕ) (e : ℕ) : ℕ := if e ∈ A then 1 else 0

def value (A : Set ℕ) : ℝ := ∑' e, (bit A e : ℝ) * haltingWeight e

def digitPrefix (A : Set ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => 4 * digitPrefix A n + bit A n

theorem bit_bounds (A : Set ℕ) (e : ℕ) : 0 ≤ (bit A e : ℝ) ∧ (bit A e : ℝ) ≤ 1 := by
  unfold bit
  split_ifs <;> norm_num

theorem weight_positive (e : ℕ) : 0 < haltingWeight e := by unfold haltingWeight; positivity

theorem weight_summable : Summable haltingWeight := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1:ℝ)/4 < 1)).mul_left (1/4)
  convert h using 1
  ext e
  simp only [haltingWeight,show (-(e+1:ℤ)) = -((e+1:ℕ):ℤ) by omega,
    zpow_neg,zpow_natCast,pow_succ,one_div,inv_pow]
  ring

theorem weight_sum : ∑' e, haltingWeight e = (1:ℝ)/3 := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1:ℝ)/4 < 1)).mul_left (1/4)
  have he : (fun e : ℕ => (1/4:ℝ) * (1/4:ℝ)^e) = haltingWeight := by
    funext e
    simp only [haltingWeight,show (-(e+1:ℤ)) = -((e+1:ℕ):ℤ) by omega,
      zpow_neg,zpow_natCast,pow_succ,one_div,inv_pow]
    ring
  rw [he] at h
  convert h.tsum_eq using 1 <;> norm_num

theorem series_summable (A : Set ℕ) : Summable (fun e => (bit A e : ℝ) * haltingWeight e) :=
  Summable.of_nonneg_of_le (fun e => mul_nonneg (bit_bounds A e).1 (le_of_lt (weight_positive e)))
    (fun e => by nlinarith [(bit_bounds A e).2,weight_positive e]) weight_summable

theorem weight_shift (j n : ℕ) : haltingWeight (j+n) = (4:ℝ)^(-(n:ℤ)) * haltingWeight j := by
  unfold haltingWeight
  rw [show -(↑(j+n)+1:ℤ) = -(n:ℤ) + -(j+1:ℤ) by push_cast; ring,
    zpow_add₀ (by norm_num : (4:ℝ) ≠ 0)]

theorem digitPrefix_value (A : Set ℕ) (n : ℕ) :
    (digitPrefix A n : ℝ) * (4:ℝ)^(-(n:ℤ)) =
      ∑ e ∈ Finset.range n, (bit A e : ℝ) * haltingWeight e := by
  induction n with
  | zero => simp [digitPrefix]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [digitPrefix, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
    unfold haltingWeight
    rw [show -(↑n+1:ℤ) = -(n:ℤ) + (-1) by ring,
      zpow_add₀ (by norm_num : (4:ℝ) ≠ 0)]
    norm_num
    ring

theorem tail_bounds (A : Set ℕ) (n : ℕ) :
    0 ≤ value A - (digitPrefix A n : ℝ) * (4:ℝ)^(-(n:ℤ)) ∧
    value A - (digitPrefix A n : ℝ) * (4:ℝ)^(-(n:ℤ)) ≤ (4:ℝ)^(-(n:ℤ))/3 := by
  have hsplit := (series_summable A).sum_add_tsum_nat_add n
  rw [← digitPrefix_value] at hsplit
  have he : value A - (digitPrefix A n : ℝ) * (4:ℝ)^(-(n:ℤ)) =
      ∑' j, (bit A (j+n) : ℝ) * haltingWeight (j+n) := by
    change _ = _
    dsimp [value]
    linarith
  rw [he]
  refine ⟨tsum_nonneg (fun j => mul_nonneg (bit_bounds A (j+n)).1
    (le_of_lt (weight_positive (j+n)))), ?_⟩
  calc
    _ ≤ ∑' j, haltingWeight (j+n) :=
      ((summable_nat_add_iff n).mpr (series_summable A)).tsum_le_tsum
        (fun j => by nlinarith [(bit_bounds A (j+n)).2, weight_positive (j+n)])
        ((summable_nat_add_iff n).mpr weight_summable)
    _ = (4:ℝ)^(-(n:ℤ))/3 := by
      simp_rw [weight_shift]
      rw [tsum_mul_left, weight_sum]
      ring

theorem theta_value : thetaK = value haltingSet := by
  unfold thetaK value bit
  congr 1
  funext e
  split_ifs <;> simp


theorem scaled_bounds (A : Set ℕ) (n : ℕ) :
    (digitPrefix A n:ℝ) ≤ value A * (4:ℝ)^n ∧
    value A * (4:ℝ)^n ≤ (digitPrefix A n:ℝ) + 1/3 := by
  have h := tail_bounds A n
  have hp : (0:ℝ) < 4^n := by positivity
  have hi : (4:ℝ)^(-(n:ℤ)) * (4:ℝ)^n = 1 := by
    simp [zpow_neg,zpow_natCast]
  have hlo := mul_nonneg h.1 (le_of_lt hp)
  have hup := mul_le_mul_of_nonneg_right h.2 (le_of_lt hp)
  simp only [sub_mul, mul_assoc, hi, mul_one] at hlo
  have hc : (4:ℝ)^(-(n:ℤ))/3 * (4:ℝ)^n = 1/3 := by
    calc _ = ((4:ℝ)^(-(n:ℤ)) * (4:ℝ)^n)/3 := by ring
         _ = 1/3 := by rw [hi]
  rw [hc] at hup
  simp only [sub_mul, mul_assoc, hi, mul_one] at hup
  constructor <;> linarith

theorem digitPrefix_mod (A : Set ℕ) (e : ℕ) : digitPrefix A (e+1) % 4 = bit A e := by
  simp only [digitPrefix, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
  unfold bit
  split_ifs <;> norm_num

theorem error_scale (e : ℕ) :
    (2:ℝ)^(-(↑(2*e+4)+1:ℤ)) * (4:ℝ)^(e+1) = 1/8 := by
  have hp : (4:ℝ)^(e+1) = (2:ℝ)^(2*(e+1)) := by rw [pow_mul]; norm_num
  rw [hp, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  rw [show -(↑(2*e+4)+1:ℤ) + ↑(2*(e+1)) = -3 by push_cast; ring]
  norm_num

theorem computable_digits (A : Set ℕ) (hc : ComputableReal (value A)) :
    ComputablePred (fun e => e ∈ A) := by
  obtain ⟨f,hf,herr⟩ := hc
  let q : ℕ → ℚ := fun e => rationalCode (f (2*e+4)) * (4:ℚ)^(e+1) + 1/4
  have hpow : Primrec (fun e : ℕ => 4^(e+1)) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow |>.comp (Primrec.const 4) Primrec.succ
  have hindex : Computable (fun e : ℕ => 2*e+4) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id) (Computable.const 4)
  have hq : Computable q :=
    rat_add.comp (rat_mul.comp (rational_decode.to_comp.comp (hf.comp hindex))
      ((rat_natCast.comp hpow.to_comp).of_eq (fun e => by simp))) (Computable.const (1/4))
  have hfloor (e : ℕ) : floorNat (q e) = digitPrefix A (e+1) := by
    have he := mul_le_mul_of_nonneg_right (herr (2*e+4))
      (by positivity : (0:ℝ) ≤ 4^(e+1))
    rw [error_scale] at he
    have hp : |(q e:ℝ) - (value A * (4:ℝ)^(e+1)+1/4)| ≤ 1/8 := by
      have heq : (q e:ℝ) - (value A*(4:ℝ)^(e+1)+1/4) =
          ((rationalCode (f (2*e+4)) : ℝ)-value A)*(4:ℝ)^(e+1) := by
        dsimp [q]
        push_cast
        ring
      rw [heq,abs_mul,abs_of_nonneg (by positivity : (0:ℝ) ≤ 4^(e+1))]
      exact he
    have hb := scaled_bounds A (e+1)
    have helo := (abs_le.mp hp).1
    have hehi := (abs_le.mp hp).2
    apply floorNat_eq
    · apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      linarith
    · apply (Rat.cast_lt (K := ℝ)).mp
      push_cast
      linarith
  have hd : Computable (fun e => floorNat (q e) % 4) :=
    Primrec.nat_mod.to_comp.comp (floorNat_computable.to_comp.comp hq) (Computable.const 4)
  have hp : ComputablePred (fun e => floorNat (q e) % 4 = 1) :=
    (Primrec.eq.decide.to_comp.comp hd (Computable.const 1)).computablePred
  exact hp.of_eq (fun e => by rw [hfloor,digitPrefix_mod]; simp [bit])

theorem halting_not_computable : ¬ ComputablePred (fun e => e ∈ haltingSet) := by
  intro h
  apply ComputablePred.halting_problem 0
  have hc : ComputablePred (fun c : Nat.Partrec.Code => encode c ∈ haltingSet) :=
    (h.decide.comp Computable.encode).computablePred
  exact hc.of_eq (fun c => by
    simp only [haltingSet, Set.mem_setOf_eq, ← Nat.Partrec.Code.ofNatCode_eq,
      Denumerable.ofNat_encode])

theorem theta_not_computable : ¬ ComputableReal thetaK := by
  rw [theta_value]
  exact fun h => halting_not_computable (computable_digits haltingSet h)

end
end E2.SeparatedDigits
