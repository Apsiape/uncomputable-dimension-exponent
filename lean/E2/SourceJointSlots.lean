import E2.JointSlots
import E2.SourceCross

namespace E2
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator

def sourceConditionalSlot {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : ℕ) : RawSlot d where
  flag := translate (sourceAt m 12) (sourceAt m 18) i
  datum := translate (sourceAt m 12) (sourceAt m 21) i
  flip := translate (sourceAt m 12) (sourceAt m 22) i
  flag_domain := translate_projection _ _ (conditional_affine_approx m true).2.2.1
    (conditional_affine_approx m true).2.1 i
  data_domain := translate_projection _ _ (conditional_affine_approx m false).2.2.1
    (conditional_affine_approx m false).2.1 i
  flip_domain := translate_reflection _ _ (conditional_affine_approx m true).2.2.1
    (by simpa [sourceDomain] using sourceAt_domain m 22 (by omega)) i
  ternary := true
  binary_flag := by simp

def sourceBinarySlot {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) (i : ℕ) : RawSlot d where
  flag := 1
  datum := 1-rawDigit (sourceClock m c) i
  flip := rawFlip (sourceClock m c) i
  flag_domain := ⟨by simp,by simp⟩
  data_domain := projection_complement (translate_projection _ _ (sourceClock_valid m c).2.2.1
    (sourceClock_valid m c).2.1 i)
  flip_domain := translate_reflection _ _ (sourceClock_valid m c).2.2.1 (sourceClock_valid m c).2.2.2 i
  ternary := false
  binary_flag := fun _ => rfl

abbrev SourceLabel (M : ℕ) := Fin M ⊕ (Fin 3 × Fin M)
def sourceLabelEquiv (M : ℕ) : SourceLabel M ≃ Fin (4*M) :=
  (Equiv.sumCongr (Equiv.refl (Fin M)) finProdFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

@[simp] theorem sourceLabel_conditional_val {M : ℕ} (i : Fin M) :
    (sourceLabelEquiv M (.inl i)).val=i.val := rfl
@[simp] theorem sourceLabel_binary_val {M : ℕ} (c : Fin 3) (i : Fin M) :
    (sourceLabelEquiv M (.inr (c,i))).val=M+c.val*M+i.val := by
  change M+(i.val+M*c.val)=_
  ac_rfl

def sourceLabelSlot {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) {M : ℕ} : SourceLabel M → RawSlot d
  | .inl i => sourceConditionalSlot m i.val
  | .inr (c,i) => sourceBinarySlot m c i.val
def sourceSlots {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (M : ℕ) (i : Fin (4*M)) : RawSlot d :=
  sourceLabelSlot m ((sourceLabelEquiv M).symm i)
@[simp] theorem sourceSlots_label {p : CounterProgram} {d M : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : SourceLabel M) :
    sourceSlots m M (sourceLabelEquiv M i)=sourceLabelSlot m i := by simp [sourceSlots]

theorem source_conditional_inclusion {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (hδ : 0 ≤ δ) (i : ℕ) :
    weighted m.state ((1-(sourceConditionalSlot m i).flag)*(sourceConditionalSlot m i).datum) ≤
      ((i:ℝ)+1)*δ := by
  have hV : Domain.unitary.Holds (sourceAt m 12) := (conditional_affine_approx m true).2.2.1
  have hF := (conditional_affine_approx m true).2.1
  have hQ := (conditional_affine_approx m false).2.1
  have hbase : weighted m.state ((1-sourceAt m 18)*sourceAt m 21) ≤ δ := by
    have h := m.defects _ (source_conditional_relation p ((1-sv p 18)*sv p 21)
      (by simp [conditionalRelations]))
    simpa [sourceAt] using h
  have hn : ‖(1-sourceAt m 18)*sourceAt m 21‖ ≤ 1 := by
    exact (norm_mul_le _ _).trans ((mul_le_mul (projection_norm_le (projection_complement hF))
      (projection_norm_le hQ) (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have ht := translate_weighted m.state (sourceAt m 12) ((1-sourceAt m 18)*sourceAt m 21)
    hV δ hδ (sourceAt_state m 12) i
  rw [translate_mul _ _ _ hV,translate_sub,translate_one _ hV] at ht
  have hm := mul_le_mul_of_nonneg_right hn (mul_nonneg (Nat.cast_nonneg i) hδ)
  change weighted m.state ((1-translate (sourceAt m 12) (sourceAt m 18) i)*
    translate (sourceAt m 12) (sourceAt m 21) i) ≤ _
  nlinarith only [ht,hbase,hm]

theorem source_conditional_states {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (hδ : 0 ≤ δ) (i : ℕ) :
    (∀ b, hs (comm ((sourceConditionalSlot m i).selected b) m.state.xi) ≤ (2*(i:ℝ)+1)*δ) ∧
    hs (comm (sourceConditionalSlot m i).flip m.state.xi) ≤ (2*(i:ℝ)+1)*δ := by
  have hV : Domain.unitary.Holds (sourceAt m 12) := (conditional_affine_approx m true).2.2.1
  have H (n : ℕ) (hn : n=18 ∨ n=21 ∨ n=22) :=
    translated_state_commutator m.state δ (sourceAt m 12) (sourceAt m n) hδ hV
      (source_conditional_variable_norm m n hn) (sourceAt_state m 12) (sourceAt_state m n) i
  refine ⟨?_,H 22 (by simp)⟩
  intro b; cases b
  · exact H 18 (by simp)
  · exact H 21 (by simp)

end
end E2
