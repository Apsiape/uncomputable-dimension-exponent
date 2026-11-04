import E2.SourceJointSlots

namespace E2
noncomputable section
open Companion.Analytic
open scoped Matrix.Norms.L2Operator

theorem source_conditional_slot_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : CounterProgram) (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ),
      0 ≤ δ → SlotBounds m.state (rawClockScale C M δ)
        (fun i : Fin M => sourceConditionalSlot m i.val) := by
  obtain ⟨Kp,hKp,hpair⟩ := source_conditional_pair_commutators
  obtain ⟨Kf,hKf,hflip⟩ := source_conditional_flips
  let L := Kp+Kf+1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hKpL : Kp ≤ L := by dsimp [L]; linarith
  have hKfL : Kf ≤ L := by dsimp [L]; linarith
  refine ⟨100*L,by linarith,?_⟩
  intro p d M δ m hδ
  let E := rawClockScale L M δ
  obtain ⟨hE,hpow,h4,h2,hrest⟩ := raw_clock_scale_bounds L δ M hδ hL
  change 0 ≤ E at hE
  have hscale : rawClockScale (100*L) M δ=100*E := by dsimp [E,rawClockScale]; ring
  rw [hscale]
  have hp (K : ℝ) (hK : 0 ≤ K) (hKL : K ≤ L) (q : ℕ) (hq : q ≤ M) : K*4^q*δ ≤ E := by
    exact (show K*4^q*δ ≤ L*4^q*δ by gcongr).trans (hpow q hq)
  have hlin (i : Fin M) : (2*(i.val:ℝ)+1)*δ ≤ 3*E := h2 i.val (Nat.le_of_lt i.isLt)
  have hlin4 (i : Fin M) : (4*(i.val:ℝ)+2)*δ ≤ 6*E := h4 i.val (Nat.le_of_lt i.isLt)
  have hsel (i : ℕ) (b : Bool) : (sourceConditionalSlot m i).selected b=
      rawDigit (conditionalClock m (!b)) i := by cases b <;> rfl
  have hpairAll (i j : Fin M) (b c : Bool) :
      weighted m.state (comm ((sourceConditionalSlot m i.val).selected b)
        ((sourceConditionalSlot m j.val).selected c)) ≤ 100*E := by
    wlog hij : i.val ≤ j.val generalizing i j b c
    · rw [weighted_comm_symm]
      exact this j i c b (by omega)
    rw [hsel,hsel]
    have h := hpair p d δ m hδ (!b) (!c) i.val j.val hij
    have hn := hp Kp (by linarith) hKpL (j.val-i.val) (by omega)
    have hi := hlin i
    nlinarith
  refine ⟨?_,?_,fun i j _ b c => hpairAll i j b c,?_,?_,?_⟩
  · intro i b
    exact ((source_conditional_states m hδ i.val).1 b).trans (by linarith [hlin i])
  · intro i
    exact (source_conditional_states m hδ i.val).2.trans (by linarith [hlin i])
  · intro i b; cases b
    · exact (source_conditional_own_flip m hδ i.val).1.trans (by linarith [hlin i])
    · have h := (source_conditional_own_flip m hδ i.val).2
      change weighted m.state (translate (sourceAt m 12) (sourceAt m 22) i.val *
        translate (sourceAt m 12) (sourceAt m 21) i.val *
        translate (sourceAt m 12) (sourceAt m 22) i.val-
        (translate (sourceAt m 12) (sourceAt m 18) i.val-
         translate (sourceAt m 12) (sourceAt m 21) i.val)) ≤ _
      apply h.trans
      have ha : (3*(i.val:ℝ)+1)*δ ≤ (4*(i.val:ℝ)+2)*δ :=
        mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith) hδ
      exact ha.trans ((hlin4 i).trans (by linarith))
  · intro i j hij b
    have hjv : i.val < j.val := hij
    cases b
    · have h := (hflip p d δ m hδ).1 i.val j.val (Nat.le_of_lt hjv)
      have hn := hp Kf (by linarith) hKfL (j.val-i.val) (by omega)
      have hi := hlin i
      exact h.trans (by nlinarith)
    · have h := (hflip p d δ m hδ).2 i.val j.val hjv
      have hn := hp Kf (by linarith) hKfL (j.val-i.val-1) (by omega)
      have hi := hlin i
      exact h.trans (by nlinarith)
  · intro i
    have h := source_conditional_inclusion m hδ i.val
    apply h.trans
    have ha : ((i.val:ℝ)+1)*δ ≤ (2*(i.val:ℝ)+1)*δ :=
      mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) i.val; linarith) hδ
    exact ha.trans ((hlin i).trans (by linarith))

end
end E2
