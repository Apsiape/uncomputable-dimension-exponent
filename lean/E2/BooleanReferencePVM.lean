import E2.BooleanRealignment

namespace E2.BooleanRealignment
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerStrategy E2.BooleanExtraction E2.CompilerDomains
variable {a d : ℕ} {G : BCSGame}

@[simp] theorem lift_zero : lift (d := d) (0 : Mat a) = 0 := by
  ext i j
  simp [lift, Matrix.reindex_apply, Matrix.kroneckerMap_apply]

@[simp] theorem lift_smul (z : ℂ) (X : Mat a) : lift (d := d) (z • X) = z • lift X := by
  ext i j
  simp [lift,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.transpose_apply,
    Matrix.smul_apply,smul_eq_mul,mul_assoc]

@[simp] theorem lift_sub (X Y : Mat a) : lift (d := d) (X-Y) = lift X - lift Y := by
  ext i j
  simp [lift,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.transpose_apply,sub_mul]

@[simp] theorem lift_sum {ι : Type*} (S : Finset ι) (f : ι → Mat a) :
    lift (d := d) (∑ i ∈ S, f i) = ∑ i ∈ S, lift (f i) := by
  ext i j
  simp [lift,Matrix.reindex_apply,Matrix.kroneckerMap_apply,Matrix.transpose_apply,
    Matrix.sum_apply,Finset.sum_mul]

def referencePVM (A : ContextPVM G a) : ContextPVM G (refSize a d) where
  value c x := lift (A.value c x)
  hermitian c x := lift_hermitian _ (A.hermitian c x)
  multiply c x y := by
    rw [← lift_mul,A.multiply]
    by_cases h : x=y
    · subst y; simp
    · simp [h,Ne.symm h]
  complete c := by rw [← lift_sum,A.complete,lift_one]
  legal c x hx := by rw [A.legal c x hx,lift_zero]

theorem reference_marginal (A : ContextPVM G a) (c v) :
    (referencePVM (d := d) A).marginal c v = lift (A.marginal c v) := by
  simp only [ContextPVM.marginal,referencePVM,lift_sum]
  apply Finset.sum_congr rfl
  intro x hx
  cases x v <;> simp

theorem reference_value (A : ContextPVM G a) (c v) :
    contextValue (referencePVM (d := d) A) c v = lift (contextValue A c v) := by
  simp only [contextValue,encodeProjection,reference_marginal,lift_sub,lift_smul,lift_one]

theorem context_signed (A : ContextPVM G a) (c v) :
    contextValue A c v = ∑ x, bitSign (x v) • A.value c x := by
  have he : (2:ℂ) • A.marginal c v - ∑ x, A.value c x =
      ∑ x, bitSign (x v) • A.value c x := by
    rw [ContextPVM.marginal,Finset.smul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    cases x v <;> simp [bitSign] <;> module
  simpa only [A.complete,contextValue,encodeProjection] using he

end
end E2.BooleanRealignment
