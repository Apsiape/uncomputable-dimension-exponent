import E2.FiniteWindowBound
import Mathlib.Algebra.BigOperators.Intervals

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators
open Fin.NatCast
attribute [local instance] Classical.propDecidable

theorem addressPeriod_dvd (N e : ℕ) (he : e < N/2) : 4^(e+1) ∣ 2^N := by
  have hpow : 4^(e+1) = 2^(2*(e+1)) := by rw [pow_mul]; norm_num
  rw [hpow]
  exact pow_dvd_pow 2 (by omega)

theorem finiteMask_mod (p : CounterProgram) (N x : ℕ) :
    finiteMask p N (x % 2^N) = finiteMask p N x := by
  unfold finiteMask
  congr 1
  apply propext
  constructor <;> rintro ⟨e,he,hd,hc⟩ <;> refine ⟨e,he,hd,?_⟩
  · simpa only [addressClass,Nat.mod_mod_of_dvd _ (addressPeriod_dvd N e (Finset.mem_range.mp he))] using hc
  · simpa only [addressClass,Nat.mod_mod_of_dvd _ (addressPeriod_dvd N e (Finset.mem_range.mp he))] using hc

theorem finiteMask_indicator (p : CounterProgram) (N x : ℕ) :
    (if finiteMask p N x then 1 else 0 : ℕ) =
      ∑ e ∈ maskIndices p N, if addressClass x e then 1 else 0 := by
  by_cases h : ∃ e ∈ maskIndices p N, addressClass x e
  · obtain ⟨e,he,hc⟩ := h
    have hf : finiteMask p N x = true := by
      simp only [finiteMask,decide_eq_true_eq]
      exact ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2,hc⟩
    rw [hf,Finset.sum_eq_single e]
    · simp [hc]
    · intro j hj hje
      exact if_neg (fun hjc => hje (addressClass_unique hjc hc))
    · exact fun hnot => False.elim (hnot he)
  · have hf : finiteMask p N x = false := by
      simp only [finiteMask,decide_eq_false_iff_not]
      rintro ⟨e,he,hd,hc⟩
      exact h ⟨e,Finset.mem_filter.mpr ⟨he,hd⟩,hc⟩
    rw [hf]
    simp only [Bool.false_eq_true,↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro e he
    exact if_neg (fun hc => h ⟨e,he,hc⟩)

theorem maskWindow_indicator (p : CounterProgram) (N x : ℕ) :
    maskWindow (maskIndices p N) x N =
      ∑ y ∈ Finset.Ico x (x+N), if finiteMask p N y then 1 else 0 := by
  rw [maskWindow_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact (finiteMask_indicator p N y).symm

theorem backwardAddress {M : ℕ} [NeZero M] (x : Fin M) (j : ℕ) :
    ((finRotate M).symm ^ j) x = x-(j:Fin M) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,finRotate_symm_apply]
    simp only [Nat.cast_add,Nat.cast_one,sub_add_eq_sub_sub]

theorem backwardAddress_val {M : ℕ} [NeZero M] (x : Fin M) {j : ℕ} (hj : j ≤ M) :
    (((finRotate M).symm ^ j) x).val = (x.val+M-j)%M := by
  rw [backwardAddress]
  have he : ((x.val+M-j:ℕ):Fin M) = x-(j:Fin M) := by
    apply (eq_sub_iff_add_eq).mpr
    apply Fin.ext
    change ((x.val+M-j)%M+j%M)%M=x.val
    rw [←Nat.add_mod,Nat.sub_add_cancel (by omega : j ≤ x.val+M),
      Nat.add_mod_right,Nat.mod_eq_of_lt x.isLt]
  rw [←he]
  rfl

/-- The backwards cyclic window equals one ordinary natural interval. -/
theorem activeWindow_mask (p : CounterProgram) (N : ℕ) (x : Fin (2^N)) :
    activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) N x =
      maskWindow (maskIndices p N) (x.val+2^N-N) N := by
  have hN : N ≤ 2^N := (Nat.lt_two_pow_self (n := N)).le
  rw [maskWindow_indicator,Finset.sum_Ico_eq_sum_range]
  have hend : x.val+2^N-N+N = x.val+2^N := by omega
  rw [show x.val+2^N-N+N-(x.val+2^N-N)=N by omega]
  unfold activeWindow
  rw [←Finset.sum_range_reflect (fun j => if finiteMask p N (x.val+2^N-N+j) then 1 else 0) N]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  dsimp only
  apply congrArg (fun b : Bool => if b then (1:ℕ) else 0)
  rw [backwardAddress_val x (j := j+1) (by omega),finiteMask_mod]
  congr 1
  omega

/-- Uniform cyclic window estimate for the actual halting mask. -/
theorem activeWindow_log_discrepancy (p : CounterProgram) (N : ℕ) (x : Fin (2^N)) :
    |(activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) N x:ℝ) -
      N*maskDensity (maskIndices p N)| ≤ Nat.log 4 N+2 := by
  rw [activeWindow_mask]
  exact maskWindow_log_discrepancy _ _ _

end
end E2.FiniteConstruction