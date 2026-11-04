import E2.CompilerPrimitives

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

def termAtom {n : ℕ} (i : Fin n) (b : Bool) : Term n :=
  .mul (.const (1/2)) (.add (.const 1) (.mul (.const (if b then 1 else -1)) (.var i)))

def termProduct {n : ℕ} (xs : List (Term n)) : Term n := xs.foldr .mul (.const 1)

@[simp] theorem termAtom_scalar {n : ℕ} (i : Fin n) (b : Bool) (a : Fin n → Bool) :
    (termAtom i b).scalar a = if a i=b then 1 else 0 := by
  cases b <;> cases h : a i <;> norm_num [termAtom,Term.scalar,sign,h]

@[simp] theorem termAtom_value {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}
    (i : Fin n) (b : Bool) (x : Fin n → A) :
    (termAtom i b).value x=CompilerMultiSelector.atom (x i) b := by
  cases b <;> simp [termAtom,Term.value,CompilerMultiSelector.atom,Algebra.smul_def,sub_eq_add_neg]

@[simp] theorem termProduct_scalar {n : ℕ} (xs : List (Term n)) (a : Fin n → Bool) :
    (termProduct xs).scalar a=(xs.map (fun t => t.scalar a)).prod := by
  induction xs with
  | nil => rfl
  | cons t xs ih => simpa only [termProduct,List.foldr_cons,Term.scalar,List.map_cons,List.prod_cons] using congrArg (t.scalar a*·) ih

@[simp] theorem termProduct_value {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}
    (xs : List (Term n)) (x : Fin n → A) :
    (termProduct xs).value x=(xs.map (fun t => t.value x)).prod := by
  induction xs with
  | nil => exact map_one _
  | cons t xs ih => simpa only [termProduct,List.foldr_cons,Term.value,List.map_cons,List.prod_cons] using congrArg (t.value x*·) ih

theorem selector_scalar {n k : ℕ} (v : Fin k → Fin n) (b : Fin k → Bool)
    (a : Fin n → Bool) :
    (termProduct (List.ofFn (fun i => termAtom (v i) (b i)))).scalar a =
      if ∀ i, a (v i)=b i then 1 else 0 := by
  classical
  simp only [termProduct_scalar,List.map_ofFn,Function.comp_def,termAtom_scalar]
  by_cases h : ∀ i, a (v i)=b i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    apply List.prod_eq_zero
    exact List.mem_ofFn.mpr ⟨i,by simp [hi]⟩

variable {V : Type*} [Fintype V] [Nonempty V]
local instance : DecidableEq V := Classical.decEq V

/-- The own-variable AND context supplies the exact selector substitution in
the same quotient as the orthogonality and gadget certificates. -/
theorem and_value (ts : List (Table V)) {k : ℕ} (out : V) (xs : Fin k → V)
    (ht : andTable out (Finset.univ.image xs) ∈ ts) :
    CompilerMultiSelector.atom (value ts out) true =
      CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value ts (xs i)) true) := by
  classical
  let v : Fin (k+1) → V := Fin.cons out xs
  let prod : Term (k+1) := termProduct (List.ofFn (fun i : Fin k => termAtom i.succ true))
  let p : Term (k+1) := .add (termAtom 0 true) (.mul (.const (-1)) prod)
  have h := table_value ts (andTable out (Finset.univ.image xs)) ht v (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [v,andTable]
    · simp [v,andTable]) p (by
    intro a ha
    have hacc : a out=true ↔ ∀ i, a (xs i)=true := by
      simpa [andTable] using ha
    change (termAtom 0 true).scalar (a ∘ v) + (-1)*(prod.scalar (a ∘ v))=0
    rw [termAtom_scalar]
    dsimp [prod]
    rw [selector_scalar]
    simp only [v,Function.comp_apply,Fin.cons_zero,Fin.cons_succ,neg_one_mul,← sub_eq_add_neg]
    by_cases h : a out=true
    · simp [h,hacc.mp h]
    · have hn : ¬ ∀ i, a (xs i)=true := fun hh => h (hacc.mpr hh)
      simp [h,hn])
  dsimp [p,Term.value] at h
  simp only [map_neg,map_one,neg_one_mul,termAtom_value,termProduct_value,List.map_ofFn] at h
  have hprod : prod.value (value ts ∘ v)=
      CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value ts (xs i)) true) := by
    simp [prod,termProduct_value,CompilerBoolean.ordered,v,Function.comp_def]
  rw [hprod] at h
  apply sub_eq_zero.mp
  simpa [v,Function.comp_def,sub_eq_add_neg] using h

variable {ι : Type*} [Fintype ι]

theorem selector_and (P : Presentation ι) (r : Fin P.relations.length) :
    CompilerMultiSelector.atom (value (tables P) (E P r)) true =
      CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true) := by
  apply and_value
  apply table_in_network P r
  simp only [relationTables,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

/-- Every source reflection commutes with every translation Z in its relation
network, derived from the game's explicit two-variable scopes. -/
theorem source_Z_commute (P : Presentation ι) (r : Fin P.relations.length)
    (s : ι × Fin 2) (i : Fin (q P r)) :
    Commute (value (tables P) (source P s)) (value (tables P) (Z P r i)) := by
  classical
  apply table_commute (tables P) (free {source P s,Z P r i})
  · apply table_in_network P r
    simp only [relationTables,List.mem_append]
    have hm : free {source P s,Z P r i} ∈
        (Finset.univ : Finset ((ι × Fin 2) × Fin (q P r))).toList.flatMap (fun si =>
          [free {source P si.1,X P r si.2},free {source P si.1,Z P r si.2}]) := by
      apply List.mem_flatMap.mpr
      exact ⟨(s,i),by simp,by simp⟩
    tauto
  · simp [free]
  · simp [free]

/-- Every successive conjugacy is supplied by its complete Boolean gadget. -/
theorem step_conjugacy (P : Presentation ι) (r : Fin P.relations.length)
    (j : Fin (steps P r)) :
    value (tables P) (control P r j.rev) *
      value (tables P) (if h : j.val=0 then E P r else conjugate P r ⟨j.val-1,by omega⟩) *
      value (tables P) (control P r j.rev)=value (tables P) (conjugate P r j) := by
  classical
  apply conjugacy_value (tables P) _ _ _
    (auxiliary P r ⟨q P r+j.val,by have := j.isLt; omega⟩)
  intro t ht
  apply table_in_network P r
  simp only [relationTables,List.mem_append]
  have hm : t ∈ (List.finRange (steps P r)).flatMap (fun j =>
      let previous := if h : j.val=0 then E P r else conjugate P r ⟨j.val-1,by omega⟩
      conjugacyTables (control P r j.rev) previous (conjugate P r j)
        (auxiliary P r ⟨q P r+j.val,by have := j.isLt; omega⟩)) :=
    List.mem_flatMap.mpr ⟨j,by simp,ht⟩
  tauto

theorem pauli_conjugacy (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r)) :
    value (tables P) (X P r i)*value (tables P) (Z P r i)*value (tables P) (X P r i)=
      value (tables P) (negZ P r i) := by
  classical
  apply conjugacy_value (tables P) _ _ _
    (auxiliary P r ⟨i.val,by have := i.isLt; omega⟩)
  intro t ht
  apply table_in_network P r
  simp only [relationTables,List.mem_append]
  have hm : t ∈ (List.finRange (q P r)).flatMap (fun j =>
      [functional {Z P r j} (negZ P r j) (by simp [negZ,Z,localWire])
        (fun a => !(a (Z P r j))) (by intro a b h; rw [h _ (by simp)])] ++
      conjugacyTables (X P r j) (Z P r j) (negZ P r j)
        (auxiliary P r ⟨j.val,by have := j.isLt; omega⟩)) := by
    apply List.mem_flatMap.mpr
    exact ⟨i,by simp,List.mem_append_right _ ht⟩
  tauto

theorem negZ_value (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r)) : value (tables P) (negZ P r i) = -value (tables P) (Z P r i) := by
  classical
  let t := functional {Z P r i} (negZ P r i) (by simp [negZ,Z,localWire])
    (fun a => !(a (Z P r i))) (by intro a b h; rw [h _ (by simp)])
  have ht : t ∈ tables P := by
    apply table_in_network P r
    simp only [relationTables,List.mem_append]
    have hm : t ∈ (List.finRange (q P r)).flatMap (fun j =>
        [functional {Z P r j} (negZ P r j) (by simp [negZ,Z,localWire])
          (fun a => !(a (Z P r j))) (by intro a b h; rw [h _ (by simp)])] ++
        conjugacyTables (X P r j) (Z P r j) (negZ P r j)
          (auxiliary P r ⟨j.val,by have := j.isLt; omega⟩)) := by
      apply List.mem_flatMap.mpr
      exact ⟨i,by simp,List.mem_append_left _ (by simp [t])⟩
    tauto
  let p : Term 2 := .add (.var 0) (.var 1)
  have h := table_value (tables P) t ht ![negZ P r i,Z P r i]
    (by intro j; fin_cases j <;> simp [t,functional]) p (by
      intro a ha
      change a (negZ P r i)=!(a (Z P r i)) at ha
      cases hb : a (Z P r i) <;> simp [p,Term.scalar,Function.comp_def,ha,hb,sign])
  have he : value (tables P) (negZ P r i)+value (tables P) (Z P r i)=0 := by
    simpa [p,Term.value,Function.comp_def] using h
  exact eq_neg_of_add_eq_zero_left he

theorem pauli_anticommutator (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r)) :
    value (tables P) (X P r i)*value (tables P) (Z P r i)+
      value (tables P) (Z P r i)*value (tables P) (X P r i)=0 := by
  have h := congrArg (fun x => x*value (tables P) (X P r i)) (pauli_conjugacy P r i)
  rw [negZ_value] at h
  have he : value (tables P) (X P r i)*value (tables P) (Z P r i)=
      -(value (tables P) (Z P r i)*value (tables P) (X P r i)) := by
    simpa only [mul_assoc,value_square,mul_one,neg_mul] using h
  rw [he,neg_add_cancel]

end
end E2.CompilerNetwork
