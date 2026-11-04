import E2.CompilerNetwork

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial
variable {V : Type*} [Fintype V] [Nonempty V]

def value (ts : List (Table V)) (v : V) : AlgebraOf (game ts) :=
  generator (game ts) (Fintype.equivFin V v)

theorem value_square (ts : List (Table V)) (v : V) : value ts v*value ts v=1 :=
  variable_square (game ts) _

/-- Any listed table is extracted from the actual game's Boolean presentation,
including variable relabeling and scope-order transport. -/
theorem table_value (ts : List (Table V)) (t : Table V) (ht : t ∈ ts) {n : ℕ}
    (v : Fin n → V) (hv : ∀ i, v i ∈ t.scope) (p : Term n)
    (hz : ∀ a, t.accepts a → p.scalar (a ∘ v)=0) :
    p.value (value ts ∘ v)=0 := by
  classical
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ht
  apply mapped_table_value (game ts) i.succ (fun j => Fintype.equivFin V (v j))
  · intro j
    change Fintype.equivFin V (v j) ∈ (ts.get i).scope.image (Fintype.equivFin V)
    rw [hi]
    exact Finset.mem_image_of_mem _ (hv j)
  · intro a ha
    have hacc : (ts.get i).accepts (fun v => a (Fintype.equivFin V v)) := by
      dsimp only [game,CompilerGame.uniform,Table.relabel,Fin.cases_succ] at ha
      exact (Finset.mem_filter.mp ha).2
    rw [hi] at hacc
    exact hz _ hacc

theorem table_commute (ts : List (Table V)) (t : Table V) (ht : t ∈ ts)
    (a b : V) (ha : a ∈ t.scope) (hb : b ∈ t.scope) : Commute (value ts a) (value ts b) := by
  classical
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp ht
  apply context_commute (game ts) i.succ
  · change Fintype.equivFin V a ∈ (ts.get i).scope.image (Fintype.equivFin V)
    rw [hi]
    exact Finset.mem_image_of_mem _ ha
  · change Fintype.equivFin V b ∈ (ts.get i).scope.image (Fintype.equivFin V)
    rw [hi]
    exact Finset.mem_image_of_mem _ hb

theorem parity_value (ts : List (Table V)) (a b c : V) (ht : parity a b c ∈ ts) :
    value ts a=value ts b*value ts c := by
  classical
  let p : Term 3 := .add (.var 0) (.mul (.const (-1)) (.mul (.var 1) (.var 2)))
  have h := table_value ts (parity a b c) ht ![a,b,c]
    (by intro i; fin_cases i <;> simp [parity]) p (by
      intro x hx
      change sign (x a)=sign (x b)*sign (x c) at hx
      simpa [p,Term.scalar,Function.comp_def,sub_eq_add_neg] using sub_eq_zero.mpr hx)
  apply sub_eq_zero.mp
  simpa [p,Term.value,Function.comp_def,sub_eq_add_neg] using h

theorem parity_last (ts : List (Table V)) (a b c : V) (ht : parity a b c ∈ ts) :
    value ts a*value ts c=value ts b := by
  rw [parity_value ts a b c ht,mul_assoc,value_square,mul_one]

theorem parity_mul (ts : List (Table V)) (a b c : V) (ht : parity a b c ∈ ts) :
    value ts a*value ts b=value ts c := by
  classical
  have hc := table_commute ts (parity a b c) ht b c (by simp [parity]) (by simp [parity])
  rw [parity_value ts a b c ht,mul_assoc,← hc.eq,← mul_assoc,value_square,one_mul]

/-- The riskiest zero-corner input follows from the two-variable orthogonality
truth table; no relation is postulated for the compiler. -/
theorem orthogonal_zero (ts : List (Table V)) (a b : V) (ht : orthogonal a b ∈ ts) :
    CompilerMultiSelector.atom (value ts a) true * CompilerMultiSelector.atom (value ts b) true=0 := by
  classical
  let atom (i : Fin 2) : Term 2 := .mul (.const (1/2)) (.add (.const 1) (.var i))
  let p : Term 2 := .mul (atom 0) (atom 1)
  have h := table_value ts (orthogonal a b) ht ![a,b]
    (by intro i; fin_cases i <;> simp [orthogonal]) p (by
      intro x hx
      change ¬ (x a=true ∧ x b=true) at hx
      by_cases ha : x a=true <;> by_cases hb : x b=true <;>
        simp_all [p,atom,Term.scalar,Function.comp_def,sign])
  dsimp [p,atom,Term.value,Function.comp_def] at h
  simp only [map_one] at h
  simpa only [CompilerMultiSelector.atom,ite_true,Algebra.smul_def] using h

/-- All seven residual inputs of the six-context converse are derived from
ordinary parity tables. -/
theorem six_conjugacy (ts : List (Table V)) (a b c : V) (d : Fin 7 → V)
    (ht : ∀ t ∈ sixTables a b c d, t ∈ ts) :
    value ts a*value ts b*value ts a=value ts c := by
  classical
  have h₁ := ht (parity a (d 0) (d 1)) (by simp [sixTables])
  have h₂ := ht (parity b (d 1) (d 2)) (by simp [sixTables])
  have h₃ := ht (parity (d 2) (d 3) (d 4)) (by simp [sixTables])
  have h₄ := ht (parity a (d 4) (d 5)) (by simp [sixTables])
  have h₅ := ht (parity c (d 5) (d 6)) (by simp [sixTables])
  have h₆ := ht (parity (d 0) (d 3) (d 6)) (by simp [sixTables])
  apply CompilerGadgets.six_context_converse _ _ _
    (value ts (d 0)) (value ts (d 1)) (value ts (d 2)) (value ts (d 3))
    (value ts (d 4)) (value ts (d 5)) (value ts (d 6))
  · exact parity_value ts _ _ _ h₁
  · exact parity_value ts _ _ _ h₂
  · exact value_square ts _
  · exact parity_value ts _ _ _ h₄
  · exact parity_last ts _ _ _ h₃
  · exact parity_mul ts _ _ _ h₆
  · have hc := table_commute ts (parity c (d 5) (d 6)) h₅ (d 5) (d 6)
      (by simp [parity]) (by simp [parity])
    exact hc.symm.eq.trans (parity_value ts _ _ _ h₅).symm

/-- Full general conjugacy, with all four remaining conjugacies discharged by
six-context Boolean gadgets in the same game. -/
theorem conjugacy_value (ts : List (Table V)) (a b c : V) (aux : GadgetWire → V)
    (ht : ∀ t ∈ conjugacyTables a b c aux, t ∈ ts) :
    value ts a*value ts b*value ts a=value ts c := by
  classical
  let x : Fin 3 → V := ![a,b,c]
  let f := aux (.inl 0)
  let y : Fin 3 → V := fun i => aux (.inl ⟨2+i.val,by omega⟩)
  let z : Fin 3 → V := fun i => aux (.inl ⟨5+i.val,by omega⟩)
  let w : Fin 3 → V := fun i => aux (.inl ⟨8+i.val,by omega⟩)
  have hm₁ (i : Fin 3) : parity (x i) (y i) (z i) ∈ ts := by
    apply ht
    unfold conjugacyTables
    simp only [List.mem_append]
    have hm := List.mem_map.mpr (show ∃ j ∈ List.finRange 3,
      parity (x j) (y j) (z j)=parity (x i) (y i) (z i) from ⟨i,by simp,rfl⟩)
    tauto
  have hm₂ (i : Fin 3) : parity (x i) f (w i) ∈ ts := by
    apply ht
    unfold conjugacyTables
    simp only [List.mem_append]
    have hm : parity (x i) f (w i) ∈ (List.finRange 3).map
        (fun j => parity (x j) f (w j)) := List.mem_map.mpr ⟨i,by simp,rfl⟩
    tauto
  have hs (i : Fin 3) : value ts f*value ts (y i)*value ts f=value ts (z i) := by
    apply six_conjugacy ts f (y i) (z i) (fun j => aux (.inr (i.castSucc,j)))
    intro t hm
    apply ht
    unfold conjugacyTables
    simp only [List.mem_append]
    have hmem : t ∈ (List.finRange 3).flatMap (fun k =>
        sixTables f (y k) (z k) (fun j => aux (.inr (k.castSucc,j)))) :=
      List.mem_flatMap.mpr ⟨i,by simp,hm⟩
    tauto
  have hs' : value ts (w 0)*value ts (y 1)*value ts (w 0)=value ts (z 2) := by
    apply six_conjugacy ts (w 0) (y 1) (z 2) (fun j => aux (.inr (3,j)))
    intro t hm
    apply ht
    unfold conjugacyTables
    simp only [List.mem_append]
    tauto
  apply CompilerGadgets.general_converse _ (value ts f) (value ts (w 0)) _ _
    (value ts (y 1)) (value ts (z 1)) (value ts (y 2)) (value ts (z 2))
  · exact value_square ts a
  · exact value_square ts f
  · exact (table_commute ts _ (hm₂ 0) a f (by simp [parity,x]) (by simp [parity])).eq
  · exact (parity_mul ts _ _ _ (hm₂ 0)).symm
  · exact hs 1
  · exact hs 2
  · exact hs'
  · exact parity_value ts _ _ _ (hm₁ 1)
  · exact parity_value ts _ _ _ (hm₁ 2)

variable {ι : Type*} [Fintype ι]

theorem table_in_network (P : Presentation ι) (r : Fin P.relations.length)
    (t : Table (Wire P)) (ht : t ∈ relationTables P r) : t ∈ tables P := by
  exact List.mem_flatMap.mpr ⟨r,by simp,ht⟩

/-- The zero-corner family for every source relation of the concrete P → G. -/
theorem zero_corner (P : Presentation ι) (r : Fin P.relations.length) :
    CompilerMultiSelector.atom (value (tables P) (E P r)) true *
      CompilerMultiSelector.atom (value (tables P) (F P r)) true=0 := by
  apply orthogonal_zero
  apply table_in_network P r
  simp only [relationTables,List.mem_append,List.mem_cons,List.not_mem_nil]
  tauto

def label (P : Presentation ι) (v : Wire P) : Fin (realize P).numVars :=
  Fintype.equivFin (Wire P) v

def cornerPolynomial (P : Presentation ι) (r : Fin P.relations.length) :
    Poly (Fin (realize P).numVars) :=
  CompilerMultiSelector.polyAtom (.var (label P (E P r))) true *
  CompilerMultiSelector.polyAtom (.var (label P (F P r))) true *
  CompilerMultiSelector.polyOrdered (fun i => .var (label P (control P r i)))

/-- The actual Q=E₀F₀S vanishes in the Boolean game's certificate quotient. -/
theorem zero_corner_certificate (P : Presentation ι) (r : Fin P.relations.length) :
    image (augmented (realize P)).relations (cornerPolynomial P r)=0 := by
  simp only [cornerPolynomial,image_mul,CompilerMultiSelector.image_atom,
    CompilerMultiSelector.image_ordered]
  change (CompilerMultiSelector.atom (value (tables P) (E P r)) true *
    CompilerMultiSelector.atom (value (tables P) (F P r)) true)*
    (CompilerBoolean.ordered (fun i => value (tables P) (control P r i)))=0
  rw [zero_corner]
  exact zero_mul _

/-- The zero-corner residual has a finite weighted certificate for the original
game, with its original dimension and state. -/
theorem zero_corner_weighted (P : Presentation ι) (r : Fin P.relations.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (η : ℝ)
      (m : Model (booleanPresentation (realize P)) d η), 0 ≤ η →
      weighted m.state (Poly.eval m.value (cornerPolynomial P r)) ≤ C*η :=
  original_weighted_bound _ _ (zero_corner_certificate P r)

end
end E2.CompilerNetwork
