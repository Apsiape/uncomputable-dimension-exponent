import E2.FiniteAddressMask
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem maskDensity_nonneg (S : Finset ℕ) : 0 ≤ maskDensity S := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem maskDensity_tail (S : Finset ℕ) (m : ℕ) (hS : ∀ e ∈ S, m < e) :
    maskDensity S ≤ (1/4:ℝ)^(m+1) := by
  let T := S.image (fun e => e-(m+1))
  have hsum : maskDensity S =
      ∑ j ∈ T, (1/4:ℝ)^(j+m+2) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro e he
      congr 1
      have := hS e he
      omega
    · intro e he j hj heq
      have := hS e he
      have := hS j hj
      dsimp only at heq
      omega
  have hgeom := (hasSum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)| < 1)).mul_left
    ((1/4:ℝ)^(m+2))
  have hle := hgeom.summable.sum_le_tsum T (fun _ _ => by positivity)
  rw [hgeom.tsum_eq] at hle
  rw [hsum]
  calc
    _ = ∑ j ∈ T, (1/4:ℝ)^(m+2)*(1/4:ℝ)^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show j+m+2=(m+2)+j by omega,pow_add]
    _ ≤ (1/4:ℝ)^(m+2)*(1-1/4)⁻¹ := hle
    _ ≤ (1/4:ℝ)^(m+1) := by
      rw [show m+2=(m+1)+1 by omega,pow_succ]
      norm_num
      have : 0 ≤ (1/4:ℝ)^(m+1) := by positivity
      nlinarith

theorem maskWindow_partition (S : Finset ℕ) (x N m : ℕ) :
    maskWindow S x N = maskWindow (S.filter (· ≤ m)) x N +
      maskWindow (S.filter (m < ·)) x N := by
  simpa only [maskWindow,not_le] using
    (Finset.sum_filter_add_sum_filter_not S (fun e => e ≤ m)
      (fun e => residueCount x N (4^e) (4^(e+1)))).symm

theorem maskDensity_partition (S : Finset ℕ) (m : ℕ) :
    maskDensity S = maskDensity (S.filter (· ≤ m)) +
      maskDensity (S.filter (m < ·)) := by
  simpa only [maskDensity,not_le] using
    (Finset.sum_filter_add_sum_filter_not S (fun e => e ≤ m)
      (fun e => (1/4:ℝ)^(e+1))).symm

/-- Uniform logarithmic discrepancy for the entire disjoint address mask.
The bound is independent of the number of admitted inputs. -/
theorem maskWindow_log_discrepancy (S : Finset ℕ) (x N : ℕ) :
    |(maskWindow S x N:ℝ) - N*maskDensity S| ≤ Nat.log 4 N + 2 := by
  let m := Nat.log 4 N
  let L := S.filter (· ≤ m)
  let H := S.filter (m < ·)
  have hH : ∀ e ∈ H, m < e := fun e he => (Finset.mem_filter.mp he).2
  have hN : N ≤ 4^(m+1) := (Nat.lt_pow_succ_log_self (by norm_num) N).le
  have hc := maskWindow_tail_le_one H x N m hH hN
  have hd := maskDensity_tail H m hH
  have hexp : (N:ℝ)*maskDensity H ≤ 1 := by
    have hnR : (N:ℝ) ≤ (4:ℝ)^(m+1) := by exact_mod_cast hN
    have hp : (4:ℝ)^(m+1)*(1/4:ℝ)^(m+1)=1 := by
      rw [←mul_pow]; norm_num
    calc
      _ ≤ (4:ℝ)^(m+1)*(1/4:ℝ)^(m+1) :=
        mul_le_mul hnR hd (maskDensity_nonneg H) (by positivity)
      _ = 1 := hp
  have htail : |(maskWindow H x N:ℝ) - N*maskDensity H| ≤ 1 := by
    have hcR : (maskWindow H x N:ℝ) ≤ 1 := by exact_mod_cast hc
    have hc0 : (0:ℝ) ≤ maskWindow H x N := by positivity
    have hd0 : 0 ≤ (N:ℝ)*maskDensity H := mul_nonneg (by positivity) (maskDensity_nonneg H)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hcard : L.card ≤ m+1 := by
    calc
      _ ≤ (Finset.range (m+1)).card := Finset.card_le_card (by
        intro e he
        exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp he).2; omega))
      _ = m+1 := Finset.card_range _
  have hsplit : (maskWindow S x N:ℝ) - N*maskDensity S =
      ((maskWindow L x N:ℝ)-N*maskDensity L)+
      ((maskWindow H x N:ℝ)-N*maskDensity H) := by
    rw [maskWindow_partition S x N m,maskDensity_partition S m,Nat.cast_add]
    dsimp [L,H]
    ring
  rw [hsplit]
  have hcardR : (L.card:ℝ) ≤ m+1 := by exact_mod_cast hcard
  calc
    _ ≤ |(maskWindow L x N:ℝ)-N*maskDensity L|+
        |(maskWindow H x N:ℝ)-N*maskDensity H| := abs_add_le _ _
    _ ≤ (L.card:ℝ)+1 := add_le_add (maskWindow_discrepancy_sum L x N) htail
    _ ≤ Nat.log 4 N+2 := by dsimp [m] at *; linarith

end
end E2.FiniteConstruction