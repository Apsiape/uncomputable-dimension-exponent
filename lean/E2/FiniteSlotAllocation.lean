import E2.FiniteBitClock

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators

/-- Number of active sites in the preceding window, for an arbitrary finite
address permutation. This includes windows crossing the cyclic boundary. -/
def activeWindow {α : Type*} (s : Equiv.Perm α) (f : α → Bool)
    (N : ℕ) (x : α) : ℕ :=
  ∑ j ∈ Finset.range N, if f ((s.symm ^ (j+1)) x) then 1 else 0

/-- The extra slot is necessary: no occupied slot in the controlled prefix may
wrap back to slot zero. -/
def slotCount {α : Type*} [Fintype α] (s : Equiv.Perm α) (f : α → Bool)
    (N : ℕ) : ℕ := 1 + Finset.univ.sup (activeWindow s f N)

theorem slotCount_pos {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (f : α → Bool) (N : ℕ) : 0 < slotCount s f N := by
  unfold slotCount
  omega

theorem activeWindow_le {α : Type*} (s : Equiv.Perm α) (f : α → Bool)
    {j N : ℕ} (hj : j ≤ N) (x : α) :
    activeWindow s f j x ≤ activeWindow s f N x := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hj)

theorem activeWindow_lt_slots {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (f : α → Bool) {j N : ℕ} (hj : j ≤ N) (x : α) :
    activeWindow s f j x < slotCount s f N := by
  have h := Finset.le_sup (f := activeWindow s f N) (Finset.mem_univ x)
  have h' := activeWindow_le s f hj x
  unfold slotCount
  omega

theorem activeWindow_pos {α : Type*} (s : Equiv.Perm α) (f : α → Bool)
    {j : ℕ} (hj : 0 < j) (x : α) (hf : f ((s.symm ^ j) x) = true) :
    0 < activeWindow s f j x := by
  have hmem : j-1 ∈ Finset.range j := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum
    (f := fun r => if f ((s.symm ^ (r+1)) x) then 1 else 0)
    (fun r (_ : r ∈ Finset.range j) => Nat.zero_le _) hmem
  simp only [show j-1+1=j by omega, hf, ↓reduceIte] at h
  exact lt_of_lt_of_le (by decide : 0 < 1) h

theorem occupiedSlot_ne_zero {α : Type*} [Fintype α] (s : Equiv.Perm α)
    (f : α → Bool) {j N : ℕ} (hj : 0 < j) (hjN : j ≤ N)
    (x : α) (hf : f ((s.symm ^ j) x) = true) :
    activeWindow s f j x % slotCount s f N ≠ 0 := by
  rw [Nat.mod_eq_of_lt (activeWindow_lt_slots s f hjN x)]
  exact Nat.ne_of_gt (activeWindow_pos s f hj x hf)

end
end E2.FiniteConstruction
