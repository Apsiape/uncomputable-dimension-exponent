import E2.CompilerBoolean

namespace E2.CompilerBoolean
noncomputable section
open scoped BigOperators
variable {d n : ℕ}

@[simp] theorem joint_cons (x : Fin (n+1) → Mat d) (b : Bool) (a : Fin n → Bool) :
    joint x (Fin.cons b a) = atom (x 0) b * joint (fun i => x i.succ) a := by
  simp [joint]

theorem all_true_iff (a : Fin n → Bool) : (∀ i, a i=true) ↔ a = fun _ => true :=
  ⟨fun h => funext h, fun h i => congrFun h i⟩

def andCoefficient (a : Fin (n+1) → Bool) : ℂ :=
  (if ∀ i : Fin n, a i.succ = true then 1 else 0) - (if a 0 then 1 else 0)

/-- Explicit finite certificate for the AND variable. Its own coordinate is
first; a finite relabeling puts it last as in `selectorAndPredicate`. -/
theorem and_certificate (x : Fin (n+1) → Mat d) :
    ∑ a, andCoefficient a • joint x a =
      joint (fun i : Fin n => x i.succ) (fun _ => true) - atom (x 0) true := by
  classical
  simp only [andCoefficient, sub_smul, Finset.sum_sub_distrib]
  congr 1
  · rw [sum_assignments_succ, Fintype.sum_bool]
    simp only [Fin.cons_succ, joint_cons, all_true_iff, ite_smul, one_smul, zero_smul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← add_mul, atom_partition, Matrix.one_mul]
  · rw [sum_assignments_succ, Fintype.sum_bool]
    simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, one_smul, zero_smul, Finset.sum_const_zero,
      add_zero, joint_cons]
    rw [← Finset.mul_sum, joint_partition, Matrix.mul_one]

theorem andCoefficient_zero (a : Fin (n+1) → Bool)
    (ha : a 0 = true ↔ ∀ i : Fin n, a i.succ = true) : andCoefficient a = 0 := by
  unfold andCoefficient
  by_cases h : a 0=true
  · simp [h, ha.mp h]
  · have ht : ¬ ∀ i : Fin n, a i.succ=true := fun h' => h (ha.mpr h')
    have hb : a 0=false := Bool.eq_false_iff.mpr h
    simp [ht, hb]

theorem andCoefficient_norm (a : Fin (n+1) → Bool) : ‖andCoefficient a‖ ≤ 1 := by
  unfold andCoefficient
  split_ifs <;> norm_num

/-- Linear weighted soundness of the own-variable AND context, before any
commutation estimate. Only forbidden joint-assignment defects enter. -/
theorem and_weighted_bound (s : State d) (x : Fin (n+1) → Mat d)
    (η : ℝ) (hη : 0 ≤ η)
    (hdef : ∀ a, ¬ (a 0=true ↔ ∀ i : Fin n, a i.succ=true) →
      weighted s (joint x a) ≤ η) :
    weighted s (joint (fun i : Fin n => x i.succ) (fun _ => true) - atom (x 0) true) ≤
      (2 : ℝ)^(n+1) * η := by
  classical
  rw [← and_certificate]
  let allowed : Finset (Fin (n+1) → Bool) :=
    Finset.univ.filter (fun a => a 0=true ↔ ∀ i : Fin n, a i.succ=true)
  have hb := forbidden_table_bound s x allowed andCoefficient η hη
    (fun a ha => andCoefficient_zero a (Finset.mem_filter.mp ha).2)
    (fun a ha => hdef a (by simpa [allowed] using ha))
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ hη
  calc
    _ ≤ ∑ _a : Fin (n+1) → Bool, (1 : ℝ) :=
      Finset.sum_le_sum (fun a _ => andCoefficient_norm a)
    _ = (2 : ℝ)^(n+1) := by simp

end
end E2.CompilerBoolean
