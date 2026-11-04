import E2.CompilerRouting

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial
variable {ι : Type*} [Fintype ι]

def selectorValue (P : Presentation ι) (r : Fin P.relations.length)
    (a : Fin (q P r) → Bool) : AlgebraOf (game (tables P)) :=
  CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (Z P r i)) (a i))

def signedSourceValue (P : Presentation ι) (r : Fin P.relations.length)
    (t : Letter (ι × Fin 2) (q P r)) : AlgebraOf (game (tables P)) :=
  let s := t.source.elim 1 (fun j => value (tables P) (source P j))
  if t.positive then s else -s

/-- The selector-controlled reflection is derived from its actual legal truth
table, for both signs and for source letters and signed constant letters. -/
theorem controlled_value (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (steps P r)) :
    value (tables P) (control P r i)=
      CompilerMultiSelector.control
        (selectorValue P r ((letters (relationWords P r)).get i).selector)
        (signedSourceValue P r ((letters (relationWords P r)).get i)) := by
  classical
  let t := (letters (relationWords P r)).get i
  let v : Fin (q P r+2) → Wire P :=
    Fin.cons (control P r i) (Fin.cons (t.source.elim (control P r i) (source P)) (Z P r))
  let e : Term (q P r+2) :=
    termProduct (List.ofFn (fun j : Fin (q P r) => termAtom j.succ.succ (t.selector j)))
  let s : Term (q P r+2) := if t.source.isSome then .var 1 else .const 1
  let a : Term (q P r+2) := if t.positive then s else .mul (.const (-1)) s
  let ctrl : Term (q P r+2) := .add (.add (.const 1) (.mul (.const (-1)) e)) (.mul e a)
  let p : Term (q P r+2) := .add (.var 0) (.mul (.const (-1)) ctrl)
  have ht : controlTable P r i ∈ tables P := by
    apply table_in_network P r
    simp only [relationTables,List.mem_append]
    have hm : controlTable P r i ∈ (List.finRange (steps P r)).map (controlTable P r) :=
      List.mem_map.mpr ⟨i,by simp,rfl⟩
    tauto
  have h := table_value (tables P) (controlTable P r i) ht v (by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [v,controlTable,functional]
    · refine Fin.cases ?_ (fun l => ?_) k
      · cases hs : t.source <;> simp [v,controlTable,functional,t,hs]
      · simp [v,controlTable,functional]) p (by
    intro x hx
    change x (control P r i) =
      (if ∀ j, x (Z P r j)=t.selector j then
        if t.positive then t.source.elim true (fun j => x (source P j))
        else !(t.source.elim true (fun j => x (source P j))) else true) at hx
    have he : e.scalar (x ∘ v)=if ∀ j, x (Z P r j)=t.selector j then 1 else 0 := by
      simpa [e,v,Function.comp_def] using
        selector_scalar (fun j : Fin (q P r) => j.succ.succ) t.selector (x ∘ v)
    have hs : s.scalar (x ∘ v)=sign (t.source.elim true (fun j => x (source P j))) := by
      cases ht' : t.source <;> simp [s,Term.scalar,v,Function.comp_def,ht',sign] <;> split_ifs <;> simp_all
    dsimp only [p,Term.scalar,ctrl]
    rw [he]
    have ha : a.scalar (x ∘ v)=if t.positive then sign (t.source.elim true (fun j => x (source P j)))
      else -sign (t.source.elim true (fun j => x (source P j))) := by
      cases hp : t.positive <;> simp [a,Term.scalar,hp,hs]
    rw [ha]
    change sign (x (control P r i)) + _=0
    rw [hx]
    by_cases hsel : ∀ j, x (Z P r j)=t.selector j
    · cases hp : t.positive <;> cases hb : t.source.elim true (fun j => x (source P j)) <;>
        norm_num [hsel,hp,hb,sign]
    · norm_num [hsel,sign])
  have he : e.value (value (tables P) ∘ v)=selectorValue P r t.selector := by
    simp [e,termProduct_value,selectorValue,CompilerBoolean.ordered,v,Function.comp_def]
  have hs : s.value (value (tables P) ∘ v)=t.source.elim 1 (fun j => value (tables P) (source P j)) := by
    cases ht' : t.source <;> simp [s,Term.value,v,Function.comp_def,ht']
  have ha : a.value (value (tables P) ∘ v)=signedSourceValue P r t := by
    cases hp : t.positive <;> simp [a,Term.value,hp,hs,signedSourceValue]
  dsimp only [p,Term.value,ctrl] at h
  rw [he,ha] at h
  apply sub_eq_zero.mp
  simpa [v,Function.comp_def,CompilerMultiSelector.control,sub_eq_add_neg] using h

end
end E2.CompilerNetwork
