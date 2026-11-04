import E2.FiniteDressedShift
import E2.FiniteConditionalSeries

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators
open Fin.NatCast

theorem activeWindow_succ {α : Type*} (s : Equiv.Perm α) (f : α → Bool) (j : ℕ) (x : α) :
    activeWindow s f (j+1) x = activeWindow s f j x +
      (if f ((s.symm^(j+1)) x) then 1 else 0) := Finset.sum_range_succ _ _

theorem skewShift_backward_power {α β : Type*} (s : Equiv.Perm α)
    (r : Equiv.Perm β) (f : α → Bool) (j : ℕ) (x : α) (b : β) :
    ((skewShift s r (fun a => if f a then 1 else 0)).symm ^ j) (x,b) =
      ((s.symm^j) x, (r ^ (-(activeWindow s f j x:ℤ))) b) := by
  induction j with
  | zero => simp [activeWindow]
  | succ j ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih]
    change (s.symm ((s.symm^j) x),
      (r ^ (-(if f (s.symm ((s.symm^j) x)) then 1 else 0 : ℤ)))
        ((r ^ (-(activeWindow s f j x:ℤ))) b)) = _
    have hs : s.symm ((s.symm^j) x) = (s.symm^(j+1)) x := by
      rw [pow_succ',Equiv.Perm.mul_apply]
    rw [hs,activeWindow_succ]
    congr 1
    change ((r ^ (-(if f ((s.symm^(j+1)) x) then 1 else 0 : ℤ)))*
      (r ^ (-(activeWindow s f j x:ℤ)))) b = _
    rw [←zpow_add]
    congr 2
    cases h : f ((s.symm^(j+1)) x) <;> simp [h] <;> omega

theorem rotateWord_power {k : ℕ} (c : ℕ) (b : Bits k) (i : Fin k) :
    ((rotateWord k)^c) b i = b (((finRotate k)^c) i) := by
  induction c generalizing b i with
  | zero => rfl
  | succ c ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    change ((rotateWord k)^c) b (finRotate k i) = _
    rw [ih,pow_succ,Equiv.Perm.mul_apply]

theorem rotateWord_at_zero {k : ℕ} [NeZero k] (c : ℕ) (b : Bits k) :
    ((rotateWord k)^c) b 0 = b (c:Fin k) := by
  rw [rotateWord_power]
  congr 1
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,finRotate_apply]
    simp

/-- Controlled optional-slot flip; it is an actual involutive permutation. -/
def optionalFlip {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool) :
    Equiv.Perm (α × Bits k) where
  toFun z := (z.1, if f z.1 then flipWord 0 z.2 else z.2)
  invFun z := (z.1, if f z.1 then flipWord 0 z.2 else z.2)
  left_inv z := by rcases z with ⟨a,b⟩; cases h : f a <;> simp [h,flipWord,Function.update_apply]
  right_inv z := by rcases z with ⟨a,b⟩; cases h : f a <;> simp [h,flipWord,Function.update_apply]

def optionalDigit {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool) (z : α × Bits k) : ℝ :=
  if f z.1 then bit z.2 0 else 0

theorem optionalDigit_bounds {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool)
    (z : α × Bits k) : 0 ≤ optionalDigit f z ∧ optionalDigit f z ≤ 1 := by
  cases h : f z.1 <;> simp only [optionalDigit,h,↓reduceIte]
  · norm_num
  · exact bit_bounds _ _

theorem optionalDigit_translate {α : Type*} {k : ℕ} [NeZero k]
    (s : Equiv.Perm α) (f : α → Bool) (j : ℕ) (x : α) (b : Bits k) :
    optionalDigit f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j) (x,b)) =
      if f ((s.symm^j) x) then bit b (activeWindow s f j x:Fin k) else 0 := by
  rw [skewShift_backward_power]
  have hr : (rotateWord k).symm ^ (-(activeWindow s f j x:ℤ)) =
      (rotateWord k) ^ (activeWindow s f j x) := by
    change ((rotateWord k)⁻¹) ^ (-(activeWindow s f j x:ℤ)) = _
    rw [inv_zpow,zpow_neg,inv_inv,zpow_natCast]
  simp only [optionalDigit,hr,bit,rotateWord_at_zero]

/-- No active translated digit in the controlled prefix occupies slot zero. -/
theorem optionalFlip_preserves_prefix {α : Type*} {k : ℕ} [NeZero k]
    (s : Equiv.Perm α) (f : α → Bool) (N : ℕ)
    (hk : ∀ x j, j ≤ N → activeWindow s f j x < k)
    (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) (z : α × Bits k) :
    optionalDigit f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j)
      (optionalFlip f z)) =
    optionalDigit f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j) z) := by
  rcases z with ⟨x,b⟩
  change optionalDigit f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j)
    (x,if f x then flipWord 0 b else b)) = _
  rw [optionalDigit_translate,optionalDigit_translate]
  by_cases hx : f x = true
  · simp only [hx,↓reduceIte]
    by_cases ha : f ((s.symm^j) x) = true
    · simp only [ha,↓reduceIte]
      apply flip_bit_other
      intro heq
      have hpos := activeWindow_pos s f (by omega : 0 < j) x ha
      have hlt := hk x j hjN
      have hval := congrArg Fin.val heq
      simp only [Fin.val_natCast,Fin.val_zero,Nat.mod_eq_of_lt hlt] at hval
      omega
    · simp only [ha,Bool.false_eq_true,↓reduceIte]
  · have hx' : f x=false := Bool.eq_false_iff.mpr hx
    simp only [hx',Bool.false_eq_true,↓reduceIte]

end
end E2.FiniteConstruction