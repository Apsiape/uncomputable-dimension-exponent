import E2.CompilerDomains

namespace E2.CompilerControlled
noncomputable section
open scoped BigOperators
open E2.CompilerBoolean

@[simp] theorem cons_one {n : ℕ} (b : Bool) (a : Fin (n+1) → Bool) :
    Fin.cons (α := fun _ => Bool) b a (1 : Fin (n+2)) = a 0 := rfl
@[simp] theorem cons_two {n : ℕ} (b : Bool) (a : Fin (n+2) → Bool) :
    Fin.cons (α := fun _ => Bool) b a (2 : Fin (n+3)) = a 1 := rfl

def sign (b : Bool) : ℂ := if b then 1 else -1

def controlAllowed (a : Fin 3 → Bool) : Prop := a 2 = if a 0 then a 1 else true

def controlCoefficient (a : Fin 3 → Bool) : ℂ :=
  sign (a 2) - (if a 0 then sign (a 1) else 1)

/-- Finite truth-table certificate for the controlled reflection, in the
order (control, source, output). No commutation hypothesis is hidden here. -/
theorem controlled_certificate {d : ℕ} (x : Fin 3 → Mat d) :
    (∑ a, controlCoefficient a • joint x a) =
      x 2 - CompilerDomains.controlled (CompilerDomains.decodeProjection (x 0)) (x 1) := by
  simp [sum_assignments_succ,Fintype.sum_bool,controlCoefficient,sign,joint,ordered,
    List.ofFn_succ,atom,CompilerDomains.controlled,CompilerDomains.decodeProjection]
  simp only [Matrix.add_mul,Matrix.mul_add,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.mul_assoc,Matrix.one_mul,Matrix.mul_one,smul_add,smul_sub,smul_smul]
  module

theorem controlCoefficient_zero (a : Fin 3 → Bool) (ha : controlAllowed a) :
    controlCoefficient a=0 := by
  unfold controlAllowed at ha
  unfold controlCoefficient
  rw [ha]
  cases h : a 0 <;> simp [h,sign]

theorem controlCoefficient_norm (a : Fin 3 → Bool) : ‖controlCoefficient a‖ ≤ 2 := by
  cases h₀ : a 0 <;> cases h₁ : a 1 <;> cases h₂ : a 2 <;>
    norm_num [controlCoefficient,sign,h₀,h₁,h₂]

theorem controlled_weighted_bound {d : ℕ} (s : State d) (x : Fin 3 → Mat d)
    (η : ℝ) (hη : 0 ≤ η)
    (hdef : ∀ a, ¬ controlAllowed a → weighted s (joint x a) ≤ η) :
    weighted s (x 2-CompilerDomains.controlled (CompilerDomains.decodeProjection (x 0)) (x 1)) ≤
      16*η := by
  classical
  rw [← controlled_certificate]
  let allowed := Finset.univ.filter controlAllowed
  have h := forbidden_table_bound s x allowed controlCoefficient η hη
    (fun a ha => controlCoefficient_zero a (Finset.mem_filter.mp ha).2)
    (fun a ha => hdef a (by simpa [allowed] using ha))
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ hη
  calc
    _ ≤ ∑ _a : Fin 3 → Bool, (2 : ℝ) :=
      Finset.sum_le_sum (fun a _ => controlCoefficient_norm a)
    _ = 16 := by norm_num

end
end E2.CompilerControlled
