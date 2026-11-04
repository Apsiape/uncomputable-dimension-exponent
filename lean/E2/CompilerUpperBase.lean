import E2.CompilerUpperProjection
import E2.CompilerNetwork

namespace E2.CompilerUpper
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerTensor E2.CompilerDomains E2.CompilerBlocks
variable {ι : Type*} {d n : ℕ}

abbrev SelectorKey (P : Presentation ι) := (r : Fin P.relations.length) × Fin (q P r)
local instance (P : Presentation ι) : DecidableEq (SelectorKey P) := Classical.decEq _

abbrev registerSize (P : Presentation ι) : ℕ := Fintype.card (Register (SelectorKey P))

theorem registerSize_pos (P : Presentation ι) : 0<registerSize P := Fintype.card_pos

@[simp] theorem selector_mul (A B : Mat n) : selector d (A*B)=selector d A*selector d B := by
  simpa only [selector,mul_one] using tensor_mul A B (1:Mat d) 1
@[simp] theorem selector_neg (A : Mat n) : selector d (-A) = -selector d A := by
  have he : Matrix.kronecker (-A) (1:Mat d) = -Matrix.kronecker A (1:Mat d) := by
    ext i j
    simp [Matrix.kronecker,Matrix.kroneckerMap]
  simp only [selector,tensor,he,map_neg]

def baseSource (P : Presentation ι) (s : ι × Fin 2 → Mat d) (j : ι × Fin 2) : Mat (registerSize P*d) :=
  E2.CompilerTensor.source (registerSize P) (s j)
def baseX (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) : Mat (registerSize P*d) :=
  selector d (pauliX (κ:=SelectorKey P) ⟨r,i⟩)
def baseZ (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) : Mat (registerSize P*d) :=
  selector d (pauliZ (κ:=SelectorKey P) ⟨r,i⟩)

theorem baseX_domain (P : Presentation ι) (r) (i) : Domain.reflection.Holds (baseX (d:=d) P r i) :=
  tensor_reflection _ 1 (pauliX_domain _) ⟨by simp,by simp⟩
theorem baseZ_domain (P : Presentation ι) (r) (i) : Domain.reflection.Holds (baseZ (d:=d) P r i) :=
  tensor_reflection _ 1 (pauliZ_domain _) ⟨by simp,by simp⟩

theorem negative_reflection (M : Mat d) (h : Domain.reflection.Holds M) : Domain.reflection.Holds (-M) := by
  exact ⟨by simp [h.1],by simpa using h.2⟩

theorem baseXX (P : Presentation ι) (r) (i j) : Commute (baseX (d:=d) P r i) (baseX P r j) := by
  change selector d _*selector d _=selector d _*selector d _
  rw [← selector_mul,← selector_mul,(pauliXX (κ:=SelectorKey P) ⟨r,i⟩ ⟨r,j⟩).eq]
theorem baseZZ (P : Presentation ι) (r) (i j) : Commute (baseZ (d:=d) P r i) (baseZ P r j) := by
  change selector d _*selector d _=selector d _*selector d _
  rw [← selector_mul,← selector_mul,(pauliZZ (κ:=SelectorKey P) ⟨r,i⟩ ⟨r,j⟩).eq]

theorem baseXZ_conjugate (P : Presentation ι) (r) (i j) :
    baseX (d:=d) P r i*baseZ P r j*baseX P r i = if i=j then -baseZ P r j else baseZ P r j := by
  unfold baseX baseZ
  rw [← selector_mul,← selector_mul,pauliXZ_conjugate]
  by_cases h : i=j
  · subst j; simp
  · have hn : (⟨r,i⟩ : SelectorKey P) ≠ ⟨r,j⟩ := by intro he; exact h (by simpa using he)
    simp [h,hn]

theorem baseXZ (P : Presentation ι) (r) (i j) (h : i≠j) :
    Commute (baseX (d:=d) P r i) (baseZ P r j) := by
  have he := baseXZ_conjugate (d:=d) P r i j
  rw [ite_eq_right h] at he
  have hc := congrArg (fun M => M*baseX P r i) he
  change baseX P r i*baseZ P r j=baseZ P r j*baseX P r i
  simpa only [mul_assoc,(baseX_domain P r i).2,mul_one] using hc

theorem baseSourceX (P : Presentation ι) (s : ι × Fin 2 → Mat d) (k) (r) (i) :
    Commute (baseSource P s k) (baseX P r i) := source_selector_commute _ _
theorem baseSourceZ (P : Presentation ι) (s : ι × Fin 2 → Mat d) (k) (r) (i) :
    Commute (baseSource P s k) (baseZ P r i) := source_selector_commute _ _

def baseE (P : Presentation ι) (r : Fin P.relations.length) : Mat (registerSize P*d) :=
  encodeProjection (E2.CompilerBoolean.joint (baseX P r) (fun _ => true))

def letterSource (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) (i : Fin (steps P r)) : Mat (registerSize P*d) :=
  let t := (letters (relationWords P r)).get i
  if t.positive then t.source.elim 1 (baseSource P s) else -(t.source.elim 1 (baseSource P s))

def baseControl (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) (i : Fin (steps P r)) : Mat (registerSize P*d) :=
  controlled (E2.CompilerBoolean.joint (baseZ P r) ((letters (relationWords P r)).get i).selector)
    (letterSource P s r i)

def baseConjugate (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) (n : ℕ) : Mat (registerSize P*d) :=
  conjugateList ((List.ofFn (fun i => baseControl P s r i.rev)).take n) (baseE P r)

theorem baseE_domain (P : Presentation ι) (r) : Domain.reflection.Holds (baseE (d:=d) P r) :=
  encode_projection _ (joint_domain _ (baseX_domain P r) (baseXX P r) _)

theorem letterSource_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (r) (i) : Domain.reflection.Holds (letterSource P s r i) := by
  have hb : Domain.reflection.Holds (((letters (relationWords P r)).get i).source.elim 1 (baseSource P s)) := by
    cases he : ((letters (relationWords P r)).get i).source with
    | none => exact ⟨by simp,by simp⟩
    | some k => simpa only [he,Option.elim_some,baseSource] using source_reflection (n:=registerSize P) (s k) (hs k)
  dsimp only [letterSource]
  split_ifs
  · exact hb
  · exact negative_reflection _ hb

theorem letterSourceZ (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r) (i) (j) :
    Commute (letterSource P s r i) (baseZ P r j) := by
  have hb : Commute (((letters (relationWords P r)).get i).source.elim 1 (baseSource P s)) (baseZ P r j) := by
    cases he : ((letters (relationWords P r)).get i).source with
    | none => simpa only [he,Option.elim_none] using Commute.one_left (baseZ (d:=d) P r j)
    | some k => simpa only [he,Option.elim_some] using baseSourceZ P s k r j
  dsimp only [letterSource]
  split_ifs
  · exact hb
  · exact hb.neg_left

theorem baseControl_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (r) (i) : Domain.reflection.Holds (baseControl P s r i) :=
  controlled_reflection _ _ (joint_domain _ (baseZ_domain P r) (baseZZ P r) _)
    (letterSource_domain P s hs r i) (commute_joint _ _ (letterSourceZ P s r i) _).symm.eq

/-- Every input of the AND context commutes with its own output reflection. -/
theorem baseX_E (P : Presentation ι) (r) (i) : Commute (baseX (d:=d) P r i) (baseE P r) := by
  unfold baseE encodeProjection
  exact ((commute_joint _ _ (baseXX P r i) _).smul_right (2:ℂ)).sub_right (Commute.one_right _)

theorem controlled_commute (M E S : Mat d) (hE : Commute M E) (hS : Commute M S) :
    Commute M (controlled E S) :=
  ((Commute.one_right M).sub_right hE).add_right (hE.mul_right hS)

/-- The selector inputs commute with the canonically defined controlled wire. -/
theorem baseZ_control (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r) (i) (j) :
    Commute (baseZ P r j) (baseControl P s r i) := by
  apply controlled_commute
  · exact commute_joint _ _ (baseZZ P r j) _
  · exact (letterSourceZ P s r i j).symm

/-- If a controlled letter has a source input, that very input commutes with
the output, without assuming commutation among different source generators. -/
theorem baseSource_control (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r) (i) (k)
    (hk : ((letters (relationWords P r)).get i).source=some k) :
    Commute (baseSource P s k) (baseControl P s r i) := by
  apply controlled_commute
  · exact commute_joint _ _ (baseSourceZ P s k r) _
  · dsimp only [letterSource]
    rw [hk]
    simp only [Option.elim_some]
    split_ifs
    · exact Commute.refl _
    · exact (Commute.refl _).neg_right

theorem baseConjugate_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (r) (n) : Domain.reflection.Holds (baseConjugate P s r n) := by
  apply conjugateList_domain
  · intro A hA
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hA)
    rw [← hi]
    exact baseControl_domain P s hs r _
  · exact baseE_domain P r

/-- This equality is the exact input for every successive conjugacy gadget. -/
theorem baseConjugate_succ (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r)
    (i : Fin (steps P r)) : baseConjugate P s r (i.val+1) =
      baseControl P s r i.rev*baseConjugate P s r i.val*baseControl P s r i.rev := by
  unfold baseConjugate
  rw [List.take_add_one,conjugateList_append]
  simp [i.isLt,conjugateList]

end
end E2.CompilerUpper
