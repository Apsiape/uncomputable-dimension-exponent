import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators

theorem permutation_map_power {α β : Type*} (s : Equiv.Perm α) (t : Equiv.Perm β)
    (read : α → β) (hread : ∀ x, read (s x)=t (read x)) (j : ℕ) (x : α) :
    read ((s^j) x)=(t^j) (read x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ',Equiv.Perm.mul_apply,hread,ih,pow_succ',Equiv.Perm.mul_apply]

theorem permutation_map_symm {α β : Type*} (s : Equiv.Perm α) (t : Equiv.Perm β)
    (read : α → β) (hread : ∀ x, read (s x)=t (read x)) (x : α) :
    read (s.symm x)=t.symm (read x) := by
  apply t.injective
  rw [←hread,s.apply_symm_apply,t.apply_symm_apply]

theorem activeWindow_map {α β : Type*} (s : Equiv.Perm α) (t : Equiv.Perm β)
    (read : α → β) (hread : ∀ x, read (s x)=t (read x)) (f : β → Bool) (N : ℕ) (x : α) :
    activeWindow s (fun a => f (read a)) N x=activeWindow t f N (read x) := by
  unfold activeWindow
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun b : Bool => if b then (1:ℕ) else 0)
  exact congrArg f (permutation_map_power s.symm t.symm read
    (permutation_map_symm s t read hread) (j+1) x)

theorem wordMask_capacity (p : CounterProgram) (N : ℕ) (b : BinaryWord N) (j : ℕ) (hj : j≤N) :
    activeWindow (incrementWord N) (wordMask p N) j b<finiteSlots p N := by
  have he : activeWindow (incrementWord N) (wordMask p N) j b=
      activeWindow (finRotate (2^N)) (fun a => finiteMask p N a.val) j (wordNumber N b) :=
    activeWindow_map (incrementWord N) (finRotate (2^N)) (wordNumber N)
      (wordNumber_increment N) (fun a => finiteMask p N a.val) j b
  rw [he]
  exact activeWindow_lt_slots _ _ hj _

theorem permutationSeries_map {α β : Type*} (s : Equiv.Perm α) (t : Equiv.Perm β)
    (read : α → β) (hread : ∀ x, read (s x)=t (read x)) (q : β → ℝ) (x : α) :
    permutationSeries s (fun a => q (read a)) x=permutationSeries t q (read x) := by
  unfold permutationSeries boundedSeries
  apply tsum_congr
  intro j
  change coefficient j*q (read ((s^j) x))=coefficient j*q ((t^j) (read x))
  rw [permutation_map_power s t read hread]

end
end E2.FiniteConstruction