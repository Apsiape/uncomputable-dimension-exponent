import E2.SourceJointConditional
import E2.SourceJointBinary
import E2.SourceJointCross

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator

/-- All unrepaired source slots satisfy one uniform budget, in the required
conditional/address/fuel/time order. -/
theorem source_joint_slot_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : CounterProgram) (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ),
      0 ≤ δ → SlotBounds m.state (rawClockScale C M δ) (sourceSlots m M) := by
  obtain ⟨Cc,hCc,hcond⟩ := source_conditional_slot_bounds
  obtain ⟨Cb,hCb,hbinary⟩ := source_binary_slot_bounds
  obtain ⟨Cx,hCx,hcross⟩ := source_conditional_compulsory_bounds
  let C := Cc+Cb+Cx
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro p d M δ m hδ
  let E := rawClockScale C M δ
  have hE : 0 ≤ E := by unfold E rawClockScale; positivity
  have h1 : rawClockScale Cc M δ ≤ E := rawClockScale_mono _ _ _ _ hδ (by dsimp [C]; linarith)
  have h2 : rawClockScale Cb M δ ≤ E := rawClockScale_mono _ _ _ _ hδ (by dsimp [C]; linarith)
  have h3 : rawClockScale Cx M δ ≤ E := rawClockScale_mono _ _ _ _ hδ (by dsimp [C]; linarith)
  have hc := (hcond p d M δ m hδ).mono h1
  have hb := (hbinary p d M δ m hδ).mono h2
  have hx n hn i j c := (hcross p d M δ m hδ n hn i j c).trans h3
  have hmixed (i j : Fin M) (c : Fin 3) (f g : Bool) :
      weighted m.state (comm ((sourceConditionalSlot m i.val).selected f)
        ((sourceBinarySlot m c j.val).selected g)) ≤ E := by
    cases g
    · change weighted m.state (comm _ 1) ≤ E
      rw [comm_one_right_eq,weighted_zero_eq]; exact hE
    · change weighted m.state (comm ((sourceConditionalSlot m i.val).selected f)
        (1-rawDigit (sourceClock m c) j.val)) ≤ E
      rw [weighted_comm_complement_right]
      cases f
      · exact hx 18 (by simp) i j c
      · exact hx 21 (by simp) i j c
  have hflipmixed (i j : Fin M) (c : Fin 3) (g : Bool) :
      weighted m.state (comm (sourceConditionalSlot m i.val).flip
        ((sourceBinarySlot m c j.val).selected g)) ≤ E := by
    cases g
    · change weighted m.state (comm _ 1) ≤ E
      rw [comm_one_right_eq,weighted_zero_eq]; exact hE
    · change weighted m.state (comm (translate (sourceAt m 12) (sourceAt m 22) i.val)
        (1-rawDigit (sourceClock m c) j.val)) ≤ E
      rw [weighted_comm_complement_right]
      exact hx 22 (by simp) i j c
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a f
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    rw [sourceSlots_label]
    rcases a with i | ⟨c,i⟩
    · exact hc.state i f
    · simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.state (finProdFinEquiv (c,i)) f
  · intro a
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    rw [sourceSlots_label]
    rcases a with i | ⟨c,i⟩
    · exact hc.flip_state i
    · simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.flip_state (finProdFinEquiv (c,i))
  · intro a b hab f g
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    obtain ⟨b,rfl⟩ := (sourceLabelEquiv M).surjective b
    rw [sourceSlots_label,sourceSlots_label]
    rcases a with i | ⟨c,i⟩ <;> rcases b with j | ⟨e,j⟩
    · exact hc.pair i j (by intro he; subst j; exact hab rfl) f g
    · exact hmixed i j e f g
    · rw [weighted_comm_symm]; exact hmixed j i c g f
    · have hne : finProdFinEquiv (c,i) ≠ finProdFinEquiv (e,j) := by
        intro he
        have hp : (c,i)=(e,j) := finProdFinEquiv.injective he
        cases hp; exact hab rfl
      simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.pair _ _ hne f g
  · intro a f
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    rw [sourceSlots_label]
    rcases a with i | ⟨c,i⟩
    · exact hc.own i f
    · simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.own (finProdFinEquiv (c,i)) f
  · intro a b hab f
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    obtain ⟨b,rfl⟩ := (sourceLabelEquiv M).surjective b
    rw [sourceSlots_label,sourceSlots_label]
    rcases a with i | ⟨c,i⟩ <;> rcases b with j | ⟨e,j⟩
    · have hh : i < j := hab
      exact hc.later i j hh f
    · exact hflipmixed i j e f
    · have hh : M+(finProdFinEquiv (c,i)).val < j.val := hab
      have := j.isLt
      omega
    · have hh : M+(finProdFinEquiv (c,i)).val < M+(finProdFinEquiv (e,j)).val := hab
      have hij : finProdFinEquiv (c,i) < finProdFinEquiv (e,j) := by change _ < _; omega
      simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.later _ _ hij f
  · intro a
    obtain ⟨a,rfl⟩ := (sourceLabelEquiv M).surjective a
    rw [sourceSlots_label]
    rcases a with i | ⟨c,i⟩
    · exact hc.inclusion i
    · simpa only [sourceBinarySlots_label,sourceLabelSlot,E] using hb.inclusion (finProdFinEquiv (c,i))

end
end E2
