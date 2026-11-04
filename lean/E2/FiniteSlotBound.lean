import E2.FiniteCyclicMask

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators

def finiteSlots (p : CounterProgram) (N : ℕ) : ℕ :=
  slotCount (finRotate (2^N)) (fun a => finiteMask p N a.val) N

theorem finiteSlots_pos (p : CounterProgram) (N : ℕ) : 0 < finiteSlots p N :=
  slotCount_pos _ _ _

theorem finiteSlots_discrepancy (p : CounterProgram) (N : ℕ) :
    |(finiteSlots p N:ℝ)-N*maskDensity (maskIndices p N)| ≤ Nat.log 4 N+3 := by
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (2^N)))
    Finset.univ_nonempty (activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) N)
  have hd := activeWindow_log_discrepancy p N x
  unfold finiteSlots slotCount
  rw [he,Nat.cast_add,Nat.cast_one]
  calc
    _ = |((activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) N x:ℝ)-
          N*maskDensity (maskIndices p N))+1| := by congr 1; ring
    _ ≤ |(activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) N x:ℝ)-
          N*maskDensity (maskIndices p N)|+|1| := abs_add_le _ _
    _ ≤ Nat.log 4 N+3 := by norm_num at *; linarith

/-- Explicit constant for the logarithmic overhead in the optional-register
exponent. This estimate also covers masks with no admitted inputs. -/
theorem finiteSlots_logb_bound (p : CounterProgram) (N : ℕ) (hN : 2 ≤ N) :
    |(finiteSlots p N:ℝ)-N*maskDensity (maskIndices p N)| ≤ 4*Real.logb 2 (N+2) := by
  have hanti : Nat.log 4 N ≤ Nat.log 2 N := Nat.log_anti_left (by norm_num) (by norm_num)
  have hlog : (Nat.log 4 N:ℝ) ≤ Real.logb 2 (N+2) := by
    calc
      _ ≤ (Nat.log 2 N:ℝ) := by exact_mod_cast hanti
      _ ≤ Real.logb 2 N := Real.natLog_le_logb _ _
      _ ≤ Real.logb 2 (N+2) := Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hone : 1 ≤ Real.logb 2 (N+2) := by
    calc
      _ = Real.logb 2 2 := by norm_num
      _ ≤ Real.logb 2 (N+2) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  exact (finiteSlots_discrepancy p N).trans (by linarith)

theorem maskDensity_eq_cutoff (p : CounterProgram) (N : ℕ) :
    maskDensity (maskIndices p N) = ∑' e, cutoff p N e := by
  rw [cutoff_eq_sum]
  simp only [maskDensity,maskIndices,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs
  · simp only [haltingWeight,show (-(e+1:ℤ)) = -((e+1:ℕ):ℤ) by omega,
      zpow_neg,zpow_natCast,one_div,inv_pow]
  · rfl
end
end E2.FiniteConstruction