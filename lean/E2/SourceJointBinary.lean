import E2.SourceJointSlots
import E2.JointScale

namespace E2
noncomputable section
open Companion.Analytic
open scoped Matrix.Norms.L2Operator

def sourceBinarySlots {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (M : ℕ) (i : Fin (3*M)) : RawSlot d :=
  let a := finProdFinEquiv.symm i
  sourceBinarySlot m a.1 a.2.val

@[simp] theorem sourceBinarySlots_label {p : CounterProgram} {d M : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) (i : Fin M) :
    sourceBinarySlots m M (finProdFinEquiv (c,i))=sourceBinarySlot m c i.val := by
  simp [sourceBinarySlots]

theorem SlotBounds.mono {d n : ℕ} {s : State d} {η β : ℝ} {x : Fin n → RawSlot d}
    (h : SlotBounds s η x) (hη : η ≤ β) : SlotBounds s β x :=
  ⟨fun i b => (h.state i b).trans hη,fun i => (h.flip_state i).trans hη,
   fun i j hij b c => (h.pair i j hij b c).trans hη,
   fun i b => (h.own i b).trans hη,fun i j hij b => (h.later i j hij b).trans hη,
   fun i => (h.inclusion i).trans hη⟩

theorem source_binary_slot_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : CounterProgram) (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ),
      0 ≤ δ → SlotBounds m.state (rawClockScale C M δ) (sourceBinarySlots m M) := by
  obtain ⟨K,hK,hraw⟩ := clock_raw_digits
  let L := K+1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hKL : K ≤ L := by dsimp [L]; linarith
  refine ⟨100*L,by linarith,?_⟩
  intro p d M δ m hδ
  let E := rawClockScale L M δ
  have hE : 0 ≤ E := by unfold E rawClockScale; positivity
  have hscale : rawClockScale (100*L) M δ=100*E := by unfold E rawClockScale; ring
  rw [hscale]
  have H (c : Fin 3) := hraw d m.state δ (sourceClock m c) M hδ (sourceClock_approx m c)
  have hbound : clockDigitError M δ K ≤ E := by
    change K*((M:ℝ)+1)^3*4^M*δ ≤ L*((M:ℝ)+1)^3*4^M*δ
    gcongr
  have hpair (c e : Fin 3) (i j : Fin M) :
      weighted m.state (comm (rawDigit (sourceClock m c) i.val) (rawDigit (sourceClock m e) j.val)) ≤ 100*E := by
    by_cases hce : c=e
    · subst e; exact ((H c).2.2.1 i.val i.isLt j.val j.isLt).trans (by linarith)
    · have hw := source_clock_cross_words m hδ c e hce 1 1 i.val j.val
      have hb := joint_word_scale L δ M i.val j.val hL hδ (by omega) (by omega)
      have he : weighted m.state (comm (rawDigit (sourceClock m c) i.val)
          (rawDigit (sourceClock m e) j.val)) ≤ 5*(2*(i.val:ℝ)+1)*(2*(j.val:ℝ)+1)*(2*i.val+2*j.val+3)*δ := by simpa [rawDigit,sourceClock] using hw
      exact he.trans (by linarith)
  have hlater (c e : Fin 3) (i j : Fin M)
      (hij : (finProdFinEquiv (c,i)).val < (finProdFinEquiv (e,j)).val) :
      weighted m.state (comm (rawFlip (sourceClock m c) i.val) (rawDigit (sourceClock m e) j.val)) ≤ 100*E := by
    by_cases hce : c=e
    · subst e
      have hij' : i.val < j.val := by change i.val+M*c.val < j.val+M*c.val at hij; omega
      exact ((H c).2.2.2.2.1 i.val i.isLt j.val j.isLt hij').trans (by linarith)
    · have hw := source_clock_cross_words m hδ c e hce 3 1 i.val j.val
      have hb := joint_word_scale L δ M i.val j.val hL hδ (by omega) (by omega)
      have he : weighted m.state (comm (rawFlip (sourceClock m c) i.val)
          (rawDigit (sourceClock m e) j.val)) ≤ 5*(2*(i.val:ℝ)+1)*(2*(j.val:ℝ)+1)*(2*i.val+2*j.val+3)*δ := by simpa [rawFlip,rawDigit,sourceClock] using hw
      exact he.trans (by linarith)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro a b
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    rw [sourceBinarySlots_label]
    cases b
    · change hs (comm (1:Mat d) m.state.xi) ≤ _
      rw [comm_one_left_eq,hs_matrix_zero]; positivity
    · change hs (comm (1-rawDigit (sourceClock m c) i.val) m.state.xi) ≤ _
      rw [state_complement]
      exact ((H c).2.2.2.2.2.1 i.val i.isLt).trans (by linarith)
  · intro a
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    rw [sourceBinarySlots_label]
    exact ((H c).2.2.2.2.2.2 i.val i.isLt).trans (by linarith)
  · intro a b _ f g
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨e,j⟩,rfl⟩ := finProdFinEquiv.surjective b
    rw [sourceBinarySlots_label,sourceBinarySlots_label]
    cases f <;> cases g
    · change weighted m.state (comm 1 1) ≤ _
      rw [comm_one_left_eq,weighted_zero_eq]; positivity
    · change weighted m.state (comm 1 _) ≤ _
      rw [comm_one_left_eq,weighted_zero_eq]; positivity
    · change weighted m.state (comm _ 1) ≤ _
      rw [comm_one_right_eq,weighted_zero_eq]; positivity
    · change weighted m.state (comm (1-rawDigit (sourceClock m c) i.val) (1-rawDigit (sourceClock m e) j.val)) ≤ _
      rw [weighted_comm_complement_left,weighted_comm_complement_right]
      exact hpair c e i j
  · intro a b
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    rw [sourceBinarySlots_label]
    let U := rawFlip (sourceClock m c) i.val
    let P := rawDigit (sourceClock m c) i.val
    have hU : Domain.reflection.Holds U := (sourceBinarySlot m c i.val).flip_domain
    cases b
    · change weighted m.state (U*1*U-1) ≤ _
      rw [Matrix.mul_one,hU.2,sub_self,weighted_zero_eq]; positivity
    · change weighted m.state (U*(1-P)*U-(1-(1-P))) ≤ _
      have he : U*(1-P)*U-(1-(1-P))= -(U*P*U-(1-P)) := by
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hU.2]; abel
      rw [he,weighted_neg]
      exact ((H c).2.2.2.1 i.val i.isLt).trans (by linarith)
  · intro a b hab f
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨e,j⟩,rfl⟩ := finProdFinEquiv.surjective b
    rw [sourceBinarySlots_label,sourceBinarySlots_label]
    cases f
    · change weighted m.state (comm _ 1) ≤ _
      rw [comm_one_right_eq,weighted_zero_eq]; positivity
    · change weighted m.state (comm (rawFlip (sourceClock m c) i.val) (1-rawDigit (sourceClock m e) j.val)) ≤ _
      rw [weighted_comm_complement_right]
      exact hlater c e i j hab
  · intro a
    obtain ⟨⟨c,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    rw [sourceBinarySlots_label]
    change weighted m.state ((1-1)*_) ≤ _
    rw [sub_self,Matrix.zero_mul,weighted_zero_eq]; positivity

end
end E2
