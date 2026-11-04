import E2.FiniteSlotAllocation

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators

/-- Address increment carrying an optional-register permutation. -/
def skewShift {α β : Type*} (s : Equiv.Perm α) (r : Equiv.Perm β)
    (f : α → ℤ) : Equiv.Perm (α × β) where
  toFun z := (s z.1, (r ^ f z.1) z.2)
  invFun z := (s.symm z.1, (r ^ (-f (s.symm z.1))) z.2)
  left_inv z := by
    rcases z with ⟨a,b⟩
    simp only [Equiv.symm_apply_apply]
    congr 1
    change ((r ^ (-f a)) * (r ^ f a)) b = b
    rw [←zpow_add,neg_add_cancel,zpow_zero]
    rfl
  right_inv z := by
    rcases z with ⟨a,b⟩
    simp only [Equiv.apply_symm_apply]
    congr 1
    change ((r ^ f (s.symm a)) * (r ^ (-f (s.symm a)))) b = b
    rw [←zpow_add,add_neg_cancel,zpow_zero]
    rfl

def dressing {α β : Type*} (r : Equiv.Perm β) (h : α → ℤ) :
    Equiv.Perm (α × β) := skewShift (Equiv.refl α) r h

theorem dressing_gauge {α β : Type*} (s : Equiv.Perm α)
    (r : Equiv.Perm β) (f h : α → ℤ) (a : α) (b : β) :
    (dressing r h).symm (skewShift s r f (dressing r h (a,b))) =
      (s a, (r ^ (h a + f a - h (s a))) b) := by
  change (s a, (r ^ (-h (s a))) ((r ^ f a) ((r ^ h a) b))) = _
  congr 1
  change ((r ^ (-h (s a))) * ((r ^ f a) * (r ^ h a))) b = _
  rw [←zpow_add,←zpow_add]
  congr 2
  omega

def flagPrefix (f : ℕ → Bool) (x : ℕ) : ℤ :=
  ∑ i ∈ Finset.range x, if f i then 1 else 0

theorem flagPrefix_zero (f : ℕ → Bool) : flagPrefix f 0 = 0 := by
  simp [flagPrefix]

theorem flagPrefix_succ (f : ℕ → Bool) (x : ℕ) :
    flagPrefix f (x+1) = flagPrefix f x + (if f x then 1 else 0) := by
  exact Finset.sum_range_succ _ _

/-- The dressed shift is ordinary increment off the last address. -/
theorem dressing_increment_interior {β : Type*} (r : Equiv.Perm β)
    (f : ℕ → Bool) (n : ℕ) (a : Fin (n+1)) (ha : a.val < n) (b : β) :
    (dressing r (fun a : Fin (n+1) => flagPrefix f a.val)).symm
      (skewShift (finRotate (n+1)) r (fun a => if f a.val then 1 else 0)
        (dressing r (fun a : Fin (n+1) => flagPrefix f a.val) (a,b))) =
      (finRotate (n+1) a,b) := by
  rw [dressing_gauge]
  have hr : (finRotate (n+1) a).val = a.val+1 := by
    exact coe_finRotate_of_ne_last (by intro he; subst a; simpa using ha)
  rw [hr,flagPrefix_succ]
  simp

/-- At the cyclic boundary exactly the total mask count remains in the gauge. -/
theorem dressing_increment_boundary {β : Type*} (r : Equiv.Perm β)
    (f : ℕ → Bool) (n : ℕ) (b : β) :
    (dressing r (fun a : Fin (n+1) => flagPrefix f a.val)).symm
      (skewShift (finRotate (n+1)) r (fun a => if f a.val then 1 else 0)
        (dressing r (fun a : Fin (n+1) => flagPrefix f a.val) (Fin.last n,b))) =
      (0,(r ^ flagPrefix f (n+1)) b) := by
  rw [dressing_gauge,finRotate_last]
  simp only [Fin.val_last,Fin.val_zero,flagPrefix_zero,sub_zero,flagPrefix_succ]

end
end E2.FiniteConstruction
