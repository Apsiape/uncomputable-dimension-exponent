import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def rawWordRotation {β : Type*} (N : ℕ) : Equiv.Perm (BinaryWord N × β) :=
  (rotateBinary N).prodCongr (Equiv.refl β)

def rawWordFlip {β : Type*} (N : ℕ) : Equiv.Perm (BinaryWord N × β) :=
  (flipFirstWord N).prodCongr (Equiv.refl β)

def rawRecursivePermutation {β : Type*} (N : ℕ) (r : Equiv.Perm β) : Equiv.Perm (BinaryWord N × β) :=
  (rawWordRotation N).trans ((twistedIncrement N r).trans
    ((rawWordRotation N).symm.trans (rawWordFlip N)))

def rawWordDigit {β : Type*} [DecidableEq β] (N : ℕ) : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ :=
  Matrix.diagonal (fun z => (boolValue (z.1.val.headD false):ℂ))

theorem listRotate_all (bs : List Bool) : (listRotate bs).all id=bs.all id := by
  cases bs <;> simp [listRotate,List.all_append,Bool.and_comm]

theorem twistedRecursive_selection {β : Type*} (N : ℕ) (hN : 0<N) (r : Equiv.Perm β)
    (z : BinaryWord N × β) :
    twistedRecursive N r z = if z.1.val.headD false then rawRecursivePermutation N r z
      else rawWordFlip N z := by
  rcases z with ⟨a,y⟩
  have hlen := a.property
  cases ha : a.val with
  | nil => simp only [ha,List.length_nil] at hlen; omega
  | cons b bs =>
    cases b
    · simp only [List.headD_cons,Bool.false_eq_true,ite_false]
      apply Prod.ext
      · apply Subtype.ext
        change recursiveIncrement a.val=listFlipFirst a.val
        simp only [ha,recursiveIncrement,listFlipFirst,Bool.not_false]
      · change (if a.val.all id then r y else y)=y
        simp [ha]
    · simp only [List.headD_cons,eq_self,ite_true]
      apply Prod.ext
      · apply Subtype.ext
        change recursiveIncrement a.val =
          listFlipFirst (listRotateBack (listIncrement (listRotate a.val)))
        simp only [ha,recursiveIncrement,listRotate]
      · change (if a.val.all id then r y else y) =
          (r ^ (if (rotateBinary N a).val.all id then 1 else 0 : ℤ)) y
        have hr : (rotateBinary N a).val.all id=a.val.all id := listRotate_all a.val
        rw [hr]
        cases h : a.val.all id <;> simp [h]

theorem permutationMatrix_trans {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Equiv.Perm α) : (Equiv.Perm.permMatrix ℂ (s.trans t))=s.permMatrix ℂ*t.permMatrix ℂ := by
  change (t*s).permMatrix ℂ=_
  exact Matrix.permMatrix_mul t s

/-- The graph of the recursive binary increment is the exact recursive matrix
expression appearing in the adjoint of the source guard relation. -/
theorem twistedRecursive_matrix {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (hN : 0<N) (r : Equiv.Perm β) :
    graphMatrix (twistedRecursive N r) =
      ((1-rawWordDigit N)+rawWordDigit N*(rawWordRotation N).permMatrix ℂ*
        (twistedIncrement N r).permMatrix ℂ*((rawWordRotation N).permMatrix ℂ).conjTranspose)*
        (rawWordFlip N).permMatrix ℂ := by
  have hp : (rawRecursivePermutation N r).permMatrix ℂ =
      (rawWordRotation N).permMatrix ℂ*(twistedIncrement N r).permMatrix ℂ*
        ((rawWordRotation N).permMatrix ℂ).conjTranspose*(rawWordFlip N).permMatrix ℂ := by
    simp only [rawRecursivePermutation,permutationMatrix_trans,Matrix.conjTranspose_permMatrix,
      Matrix.mul_assoc]
    rfl
  have he : ((1-rawWordDigit N)+rawWordDigit N*(rawWordRotation N).permMatrix ℂ*
      (twistedIncrement N r).permMatrix ℂ*((rawWordRotation N).permMatrix ℂ).conjTranspose)*
      (rawWordFlip N).permMatrix ℂ =
      (1-rawWordDigit N)*(rawWordFlip N).permMatrix ℂ+
        rawWordDigit N*(rawRecursivePermutation N r).permMatrix ℂ := by
    rw [hp]
    noncomm_ring
  rw [he,←graphMatrix_perm,←graphMatrix_perm]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_mul,Matrix.one_mul,Matrix.sub_apply,
    rawWordDigit,Matrix.diagonal_mul]
  cases h : i.1.val.headD false <;>
    simp only [graphMatrix,twistedRecursive_selection N hN r i,h,boolValue,ite_true,ite_false,
      Bool.false_eq_true,eq_self,Complex.ofReal_zero,Complex.ofReal_one,
      zero_mul,one_mul,sub_zero,sub_self,zero_add,add_zero]

theorem raw_guard_operator_bound {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (hN : 0<N) (r : Equiv.Perm β) :
    ‖coordinateGuard N*((twistedIncrement N r).permMatrix ℂ-
      ((1-rawWordDigit N)+rawWordDigit N*(rawWordRotation N).permMatrix ℂ*
        (twistedIncrement N r).permMatrix ℂ*((rawWordRotation N).permMatrix ℂ).conjTranspose)*
        (rawWordFlip N).permMatrix ℂ)‖ ≤ 2*(1/4:ℝ)^N := by
  rw [←twistedRecursive_matrix N hN r]
  exact twisted_guard_norm N r

end
end E2.FiniteConstruction