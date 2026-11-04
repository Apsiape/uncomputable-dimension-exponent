import E2.CompilerSourceRealize

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

section Frames
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem atom_mul (x : A) (hx : x*x=1) (a b : Bool) :
    CompilerMultiSelector.atom x a*CompilerMultiSelector.atom x b=
      if a=b then CompilerMultiSelector.atom x a else 0 := by
  cases a <;> cases b <;>
    simp only [CompilerMultiSelector.atom,↓reduceIte,Bool.false_eq_true,Bool.true_eq_false,
      Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,
      mul_add,mul_sub,add_mul,sub_mul,mul_one,one_mul,hx]
  all_goals module

theorem selector_orthogonality {n : ℕ} (Z : Fin n → A)
    (hZ : ∀ i, Z i*Z i=1) (hc : ∀ i j, Commute (Z i) (Z j))
    (a b : Fin n → Bool) :
    joint Z a*joint Z b=if a=b then joint Z a else 0 := by
  classical
  unfold joint
  rw [CompilerMultiSelector.ordered_mul _ _ (fun i j _ =>
    CompilerMultiSelector.atom_commute _ _ (hc i j) _ _)]
  simp_rw [atom_mul _ (hZ _)]
  by_cases h : a=b
  · subst b
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    apply List.prod_eq_zero
    exact List.mem_ofFn.mpr ⟨i,by simp [hi]⟩

end Frames

variable {ι : Type*} [Fintype ι]

theorem XX_commute (P : Presentation ι) (r : Fin P.relations.length)
    (i j : Fin (q P r)) : Commute (value (tables P) (X P r i)) (value (tables P) (X P r j)) := by
  classical
  apply table_commute (tables P) (free (Finset.univ.image (X P r)))
  · apply table_in_network P r
    simp only [relationTables,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto
  · simp [free]
  · simp [free]

theorem ZZ_commute (P : Presentation ι) (r : Fin P.relations.length)
    (i j : Fin (q P r)) : Commute (value (tables P) (Z P r i)) (value (tables P) (Z P r j)) := by
  classical
  apply table_commute (tables P) (free (Finset.univ.image (Z P r)))
  · apply table_in_network P r
    simp only [relationTables,List.mem_append,List.mem_cons,List.not_mem_nil]
    tauto
  · simp [free]
  · simp [free]

theorem XZ_commute (P : Presentation ι) (r : Fin P.relations.length)
    (i j : Fin (q P r)) (hij : i ≠ j) :
    Commute (value (tables P) (X P r i)) (value (tables P) (Z P r j)) := by
  classical
  apply table_commute (tables P) (free {X P r i,Z P r j})
  · apply table_in_network P r
    simp only [relationTables,List.mem_append]
    have hm : free {X P r i,Z P r j} ∈
        (Finset.univ : Finset (Fin (q P r) × Fin (q P r))).toList.flatMap (fun ij =>
          if ij.1=ij.2 then [] else [free {X P r ij.1,Z P r ij.2}]) := by
      apply List.mem_flatMap.mpr
      exact ⟨(i,j),by simp,by simp [hij]⟩
    tauto
  · simp [free]
  · simp [free]

theorem source_X_commute (P : Presentation ι) (r : Fin P.relations.length)
    (s : ι × Fin 2) (i : Fin (q P r)) :
    Commute (value (tables P) (source P s)) (value (tables P) (X P r i)) := by
  classical
  apply table_commute (tables P) (free {source P s,X P r i})
  · apply table_in_network P r
    simp only [relationTables,List.mem_append]
    have hm : free {source P s,X P r i} ∈
        (Finset.univ : Finset ((ι × Fin 2) × Fin (q P r))).toList.flatMap (fun si =>
          [free {source P si.1,X P r si.2},free {source P si.1,Z P r si.2}]) := by
      apply List.mem_flatMap.mpr
      exact ⟨(s,i),by simp,by simp⟩
    tauto
  · simp [free]
  · simp [free]

theorem selectors_partition (P : Presentation ι) (r : Fin P.relations.length) :
    ∑ a, selectorValue P r a=1 := joint_partition _

theorem selectors_orthogonal (P : Presentation ι) (r : Fin P.relations.length)
    (a b : Fin (q P r) → Bool) :
    selectorValue P r a*selectorValue P r b=if a=b then selectorValue P r a else 0 :=
  selector_orthogonality _ (fun i => value_square _ _) (ZZ_commute P r) a b

theorem realized_compression (P : Presentation ι) (r : Fin P.relations.length)
    (a : Fin (q P r) → Bool) :
    CompilerMultiSelector.atom (value (tables P) (E P r)) true * selectorValue P r a *
      CompilerMultiSelector.atom (value (tables P) (E P r)) true =
    ((1/2:ℚ)^(q P r)) • CompilerMultiSelector.atom (value (tables P) (E P r)) true := by
  rw [selector_and]
  exact CompilerMultiSelector.pauli_multi_compression _ _ (fun i => value_square _ _)
    (pauli_anticommutator P r) (fun i j _ => XX_commute P r i j) (XZ_commute P r) a

theorem realized_twirl (P : Presentation ι) (r : Fin P.relations.length) :
    (∑ a : Fin (q P r) → Bool,
      CompilerMultiSelector.translate (fun i => value (tables P) (Z P r i)) a *
        CompilerMultiSelector.atom (value (tables P) (E P r)) true *
      CompilerMultiSelector.reverseTranslate (fun i => value (tables P) (Z P r i)) a)=1 := by
  rw [selector_and]
  exact CompilerMultiSelector.pauli_multi_twirl _ _ (fun i => value_square _ _)
    (pauli_anticommutator P r) (XZ_commute P r)

theorem source_selector_commute (P : Presentation ι) (r : Fin P.relations.length)
    (s : ι × Fin 2) (a : Fin (q P r) → Bool) :
    Commute (value (tables P) (source P s)) (selectorValue P r a) := by
  apply CompilerMultiSelector.commute_ordered
  intro i
  cases a i <;> simp only [CompilerMultiSelector.atom,↓reduceIte,Bool.false_eq_true]
  · exact ((Commute.one_right _).sub_right (source_Z_commute P r s i)).smul_right _
  · exact ((Commute.one_right _).add_right (source_Z_commute P r s i)).smul_right _

/-- The actual controlled word is routed through the actual selector partition.
No partition, orthogonality, or commutation certificate remains an input. -/
theorem realized_word_routing (P : Presentation ι) (r : Fin P.relations.length) :
    wordValue P r=CompilerMultiSelector.blockSum (selectorValue P r)
      (fun a => ((letters (relationWords P r)).map (fun t =>
        if a=t.selector then signedSourceValue P r t else 1)).prod) := by
  classical
  have he : List.ofFn (fun i => value (tables P) (control P r i))=
      (letters (relationWords P r)).map (fun t =>
        CompilerMultiSelector.control (selectorValue P r t.selector) (signedSourceValue P r t)) := by
    calc
      _ = List.ofFn (fun i => CompilerMultiSelector.control
          (selectorValue P r ((letters (relationWords P r)).get i).selector)
          (signedSourceValue P r ((letters (relationWords P r)).get i))) := by
            congr 1
            funext i
            exact controlled_value P r i
      _ = _ := by
        have hh := List.ofFn_comp' (letters (relationWords P r)).get
          (fun t => CompilerMultiSelector.control (selectorValue P r t.selector) (signedSourceValue P r t))
        rw [List.ofFn_get] at hh
        exact hh
  unfold wordValue CompilerBoolean.ordered
  rw [he]
  have h := CompilerMultiSelector.controlled_word_blocks (selectorValue P r)
    (selectors_partition P r) (selectors_orthogonal P r)
    ((letters (relationWords P r)).map (fun t => (t.selector,signedSourceValue P r t))) (by
      intro t ht a
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
      dsimp only [signedSourceValue]
      cases hp : u.positive <;> cases hs : u.source <;> simp only [hp,↓reduceIte,hs,Option.elim_none,Option.elim_some]
      · exact (Commute.one_left _).neg_left
      · exact (source_selector_commute P r _ a).neg_left
      · exact Commute.one_left _
      · exact source_selector_commute P r _ a)
  simpa only [q,steps,List.map_map,Function.comp_def] using h

end
end E2.CompilerNetwork
