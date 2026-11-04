import E2.CompilerUpperFunctionalTables

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks
variable {ι : Type*} [Fintype ι] {d n : ℕ}
local instance (P : Presentation ι) : DecidableEq (Wire P) := Classical.decEq _

theorem duplicate_commute (A B : Mat d) (h : Commute A B) : Commute (duplicate A) (duplicate B) := by
  change duplicate A*duplicate B=duplicate B*duplicate A
  rw [← duplicate_mul,← duplicate_mul,h.eq]

@[simp] theorem duplicate_atom (X : Mat d) (b : Bool) :
    duplicate (E2.CompilerBoolean.atom X b)=E2.CompilerBoolean.atom (duplicate X) b := by
  cases b <;> simp [E2.CompilerBoolean.atom]

@[simp] theorem duplicate_joint (x : Fin n → Mat d) (a : Fin n → Bool) :
    duplicate (E2.CompilerBoolean.joint x a)=E2.CompilerBoolean.joint (fun i => duplicate (x i)) a := by
  induction n with
  | zero => simp [E2.CompilerBoolean.joint,E2.CompilerBoolean.ordered]
  | succ n ih =>
    unfold E2.CompilerBoolean.joint
    rw [E2.CompilerBoolean.ordered_succ,E2.CompilerBoolean.ordered_succ,duplicate_mul,duplicate_atom]
    congr 1
    exact ih (fun i => x i.succ) (fun i => a i.succ)

theorem wireValue_E_joint (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) :
    wireValue P s aux (E P r)=encodeProjection
      (E2.CompilerBoolean.joint (fun i => wireValue P s aux (X P r i)) (fun _ => true)) := by
  simp [baseE,wireValue_E,encodeProjection,duplicate_joint]

/-- The actual AND context has exact marginals in the common wire space. -/
theorem actual_and_measurement (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) :
    ∃ A : TableMeasurement (andTable (E P r) (Finset.univ.image (X P r))) (2*(2*(registerSize P*d))),
      ∀ v ∈ (andTable (E P r) (Finset.univ.image (X P r))).scope,
        A.marginal v=decodeProjection (wireValue P s aux v) := by
  apply and_measurement
  · intro i; rw [wireValue_X]; exact duplicate_domain _ _ (duplicate_domain _ _ (baseX_domain P r i))
  · intro i j; simp only [wireValue_X]; exact duplicate_commute _ _ (duplicate_commute _ _ (baseXX P r i j))
  · exact wireValue_E_joint P s aux r

/-- The actual negated-Z context has exact marginals. -/
theorem actual_negation_measurement (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (hdom : ∀ w, Domain.reflection.Holds (wireValue P s aux w)) (r) (i : Fin (q P r)) :
    ∃ A : TableMeasurement (functional {Z P r i} (negZ P r i)
      (by simp [negZ,Z,localWire]) (fun a => !(a (Z P r i)))
      (by intro a b h; rw [h _ (by simp)])) (2*(2*(registerSize P*d))),
      ∀ v ∈ insert (negZ P r i) ({Z P r i}:Finset (Wire P)),
        A.marginal v=decodeProjection (wireValue P s aux v) := by
  apply negation_measurement
  · exact fun w _ => hdom w
  · simp

/-- The controlled wire formula after both ancillary doublings. -/
theorem wireValue_control_formula (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (r) (i : Fin (steps P r)) :
    wireValue P s aux (control P r i)=
      controlled (E2.CompilerBoolean.joint (fun j => wireValue P s aux (Z P r j))
        ((letters (relationWords P r)).get i).selector)
      (if ((letters (relationWords P r)).get i).positive then
        ((letters (relationWords P r)).get i).source.elim 1 (fun k => wireValue P s aux (source P k))
       else -(((letters (relationWords P r)).get i).source.elim 1 (fun k => wireValue P s aux (source P k)))) := by
  rw [wireValue_control]
  unfold baseControl letterSource
  simp only [List.get_eq_getElem]
  cases hp : ((letters (relationWords P r))[i.val]).positive <;>
    cases hs : ((letters (relationWords P r))[i.val]).source <;>
    simp [hp,hs,controlled,duplicate_joint]

/-- Every incidence of the actual controlled Boolean table has its exact marginal. -/
theorem actual_control_measurement (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (hdom : ∀ w, Domain.reflection.Holds (wireValue P s aux w))
    (r) (i : Fin (steps P r)) :
    ∃ A : TableMeasurement (controlTable P r i) (2*(2*(registerSize P*d))),
      ∀ v ∈ (controlTable P r i).scope,
        A.marginal v=decodeProjection (wireValue P s aux v) := by
  classical
  let t := (letters (relationWords P r)).get i
  let x := wireValue P s aux
  have hs (v : Wire P) : v ∈ (controlTable P r i).scope ↔
      v=control P r i ∨ (∃ j, Z P r j=v) ∨ ∃ k, t.source=some k ∧ source P k=v := by
    simp [controlTable,functional,t,Option.mem_toList]
  have hZZ (j k) : Commute (x (Z P r j)) (x (Z P r k)) :=
    duplicate_commute _ _ (duplicate_commute _ _ (baseZZ P r j k))
  have hZS (j k) : Commute (x (Z P r j)) (x (source P k)) :=
    (duplicate_commute _ _ (duplicate_commute _ _ (baseSourceZ P s k r j))).symm
  have hZC (j) : Commute (x (Z P r j)) (x (control P r i)) :=
    duplicate_commute _ _ (duplicate_commute _ _ (baseZ_control P s r i j))
  have hSC (k) (hk : t.source=some k) : Commute (x (source P k)) (x (control P r i)) :=
    duplicate_commute _ _ (duplicate_commute _ _ (baseSource_control P s r i k hk))
  apply exact_table_measurement
  · exact fun v _ => hdom v
  · intro v hv w hw
    rcases (hs v).mp hv with rfl | ⟨j,rfl⟩ | ⟨k,hk,rfl⟩ <;>
      rcases (hs w).mp hw with rfl | ⟨l,rfl⟩ | ⟨m,hm,rfl⟩
    · exact Commute.refl _
    · exact (hZC l).symm
    · exact (hSC m hm).symm
    · exact hZC j
    · exact hZZ j l
    · exact hZS j m
    · exact hSC k hk
    · exact (hZS l k).symm
    · have he : k=m := Option.some.inj (hk.symm.trans hm)
      subst m
      exact Commute.refl _
  · intro a J he hbad
    have hz (j) := he (Z P r j) ((hs _).mpr (Or.inr (Or.inl ⟨j,rfl⟩)))
    have hsrc (k) (hk : t.source=some k) :=
      he (source P k) ((hs _).mpr (Or.inr (Or.inr ⟨k,hk,rfl⟩)))
    have hc := controlled_eigen_on (Z P r) (t.source.map (source P)) t.positive t.selector x a J hz (by
      intro v hv
      obtain ⟨k,hk,hv⟩ := Option.map_eq_some_iff.mp hv
      subst v
      exact hsrc k hk)
    have hout := he (control P r i) (by simp [controlTable,functional])
    rw [wireValue_control_formula] at hout
    simp only [Option.elim_map] at hc
    change _=(E2.CompilerRealize.sign (a (control P r i)):ℂ) • J at hout
    have hh := hc.symm.trans hout
    apply scalar_eigen_zero J _ _ hh
    intro heq
    apply hbad
    dsimp only [controlTable,functional]
    have hval := sign_injective heq.symm
    by_cases hz : ∀ j, a (Z P r j)=t.selector j
    · simpa [t,hz,Function.comp_def] using hval
    · simpa [t,hz,Function.comp_def] using hval

end
end E2.CompilerUpper

