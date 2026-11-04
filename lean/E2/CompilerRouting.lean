import E2.CompilerCorner

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

section Chain
variable {A : Type*} [Ring A]

theorem conjugacy_chain {n : ℕ} (C : Fin n → A) (D : Fin (n+1) → A)
    (h : ∀ i, D i.succ=C i*D i.castSucc*C i) :
    D (Fin.last n)=(List.ofFn C).reverse.prod*D 0*(List.ofFn C).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he := ih (fun i => C i.castSucc) (fun i => D i.castSucc)
      (fun i => h i.castSucc)
    have hl := h (Fin.last n)
    rw [← Fin.succ_last,hl,he]
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append,List.reverse_append,List.reverse_singleton,
      List.prod_append,List.prod_singleton]
    simp only [mul_assoc,Fin.castSucc_zero]

theorem reverse_involutions (xs : List A) (h : ∀ a ∈ xs, a*a=1) :
    xs.reverse.prod*xs.prod=1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.reverse_cons,List.prod_append,List.prod_singleton,List.prod_cons,List.prod_nil,mul_one,one_mul]
    calc
      _ = xs.reverse.prod*(a*a)*xs.prod := by simp only [mul_assoc]
      _ = 1 := by rw [h a (by simp),mul_one]; exact ih (fun b hb => h b (by simp [hb]))

theorem forward_involutions (xs : List A) (h : ∀ a ∈ xs, a*a=1) :
    xs.prod*xs.reverse.prod=1 := by
  simpa only [List.reverse_reverse] using reverse_involutions xs.reverse
    (fun a ha => h a (List.mem_reverse.mp ha))

theorem ofFn_rev {n : ℕ} (C : Fin n → A) : List.ofFn (fun i => C i.rev)=(List.ofFn C).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_reverse,List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

end Chain

variable {ι : Type*} [Fintype ι]

def wordValue (P : Presentation ι) (r : Fin P.relations.length) : AlgebraOf (game (tables P)) :=
  CompilerBoolean.ordered (fun i => value (tables P) (control P r i))

def reverseWordValue (P : Presentation ι) (r : Fin P.relations.length) : AlgebraOf (game (tables P)) :=
  (List.ofFn (fun i => value (tables P) (control P r i))).reverse.prod

/-- Every successive reflection conjugacy is assembled, including an empty
word, into the final F variable of the actual network. -/
theorem final_conjugacy (P : Presentation ι) (r : Fin P.relations.length) :
    value (tables P) (F P r)=wordValue P r*value (tables P) (E P r)*reverseWordValue P r := by
  let C : Fin (steps P r) → AlgebraOf (game (tables P)) :=
    fun j => value (tables P) (control P r j.rev)
  let D : Fin (steps P r+1) → AlgebraOf (game (tables P)) := fun j =>
    value (tables P) (if h : j.val=0 then E P r else conjugate P r ⟨j.val-1,by have := j.isLt; omega⟩)
  have hD (j : Fin (steps P r)) : D j.succ=value (tables P) (conjugate P r j) := by
    simp [D]
  have h : ∀ j, D j.succ=C j*D j.castSucc*C j := by
    intro j
    rw [hD]
    exact (step_conjugacy P r j).symm
  have hc := conjugacy_chain C D h
  have hC : List.ofFn C=(List.ofFn (fun i => value (tables P) (control P r i))).reverse :=
    ofFn_rev (fun i => value (tables P) (control P r i))
  rw [hC,List.reverse_reverse] at hc
  simpa only [D,F,Fin.val_last,Fin.val_zero,↓reduceDIte,wordValue,reverseWordValue,
    CompilerBoolean.ordered] using hc

theorem word_inverse (P : Presentation ι) (r : Fin P.relations.length) :
    reverseWordValue P r*wordValue P r=1 ∧ wordValue P r*reverseWordValue P r=1 := by
  have h : ∀ a ∈ List.ofFn (fun i => value (tables P) (control P r i)), a*a=1 := by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact value_square _ _
  exact ⟨reverse_involutions _ h,forward_involutions _ h⟩

/-- The gadget and AND substitutions give the entire E₀F₀S → E_pol S E_pol
corner substitution. The remaining normalization to the source p is separate. -/
theorem conjugate_corner_substitution (P : Presentation ι) (r : Fin P.relations.length) :
    CompilerMultiSelector.atom (value (tables P) (E P r)) true *
      CompilerMultiSelector.atom (value (tables P) (F P r)) true * wordValue P r =
    (CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true)) *
      wordValue P r *
    (CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true)) := by
  have hF : CompilerMultiSelector.atom (value (tables P) (F P r)) true=
      wordValue P r*CompilerMultiSelector.atom (value (tables P) (E P r)) true*reverseWordValue P r := by
    rw [final_conjugacy]
    simp only [CompilerMultiSelector.atom,↓reduceIte,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    congr 1
    rw [mul_add,mul_one,add_mul,(word_inverse P r).2]
  rw [hF,CompilerSelector.conjugate_corner _ _ _ (word_inverse P r).1,selector_and]

end
end E2.CompilerNetwork
