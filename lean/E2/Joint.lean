import E2.Carry
import E2.MeasurementDefs
import E2.RawWords
import E2.TernaryRepair
import E2.SourceClock
import E2.ConditionalCommutations
import E2.SourceCross
import E2.JointAssemblyTools

namespace E2
noncomputable section

def modelValue {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (n : ℕ) : Mat d := Poly.eval m.value (sv p n)
def modelClock {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) : ClockData d :=
  ⟨modelValue m (4*c.val), modelValue m (4*c.val+1),
   modelValue m (4*c.val+2), modelValue m (4*c.val+3)⟩

theorem modelClock_approx {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) : ClockApprox m.state δ (modelClock m c) := by
  simpa only [modelClock,modelValue,sourceClock,sourceAt] using sourceClock_approx m c

theorem model_address_approx {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) :
    AddressApprox m.state δ (modelClock m 0) (modelValue m 12) (modelValue m 14) := by
  simpa only [modelClock,modelValue,sourceClock,sourceAt] using source_address_approx m
def jointError (M : ℕ) (δ C : ℝ) : ℝ := C*(M+1)^6*4^M*δ

/-- The ordering is conditional measurements, address, fuel, then time.
The compulsory effects are exactly the raw conjugated digit projections. -/
structure JointFamily {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (M : ℕ) (C : ℝ) where
  measurement : Fin (4*M) → Measurement d
  unitary : Fin (4*M) → Mat d
  repairedQ : Fin M → Mat d
  conditional : ∀ i : Fin M,
    ∃ j : Fin (4*M), j.val=i.val ∧
      (measurement j).outcomes=3 ∧
      (measurement j).projection ((measurement j).index 0) = 1-translate (modelValue m 12) (modelValue m 18) i.val ∧
      (measurement j).projection ((measurement j).index 1) = translate (modelValue m 12) (modelValue m 18) i.val-repairedQ i ∧
      (measurement j).projection ((measurement j).index 2) = repairedQ i ∧
      unitary j = translate (modelValue m 12) (modelValue m 22) i.val
  compulsory : ∀ c : Fin 3, ∀ k : Fin M,
    ∃ j : Fin (4*M), j.val=M+c.val*M+k.val ∧
      (measurement j).outcomes=2 ∧
      (measurement j).projection ((measurement j).index 0) = rawDigit (modelClock m c) k.val ∧
      (measurement j).projection ((measurement j).index 1) = 1-rawDigit (modelClock m c) k.val ∧
      unitary j = rawFlip (modelClock m c) k.val
  repaired_close : ∀ i, weighted m.state (repairedQ i - translate (modelValue m 12) (modelValue m 21) i.val) ≤
    C*jointError M δ C
  relations : TriangularRelations m.state (jointError M δ C) measurement unitary

/-- Lemma 9.3. Constants are independent of the program, dimension, state,
precision and growing depth. Cross-clock commutators route through raw words. -/
theorem joint_measurements : ∃ C : ℝ, 0 < C ∧ ∀ (p : CounterProgram) (d M : ℕ)
    (δ : ℝ) (m : Model (sourcePresentation p) d δ), 1 ≤ M → 0 ≤ δ →
    Nonempty (JointFamily m M C) := by
  obtain ⟨K,hK,hraw⟩ := source_joint_slot_bounds
  let C := 256*K
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,by linarith,?_⟩
  intro p d M δ m _hM hδ
  let E := rawClockScale K M δ
  have hE : 0 ≤ E := by unfold E rawClockScale; positivity
  obtain ⟨y,hkeep,hbinary,hclose,hbounds⟩ :=
    repair_slots m.state E hE (sourceSlots m M) (hraw p d M δ m hδ)
  have hη : 4*(53*E) ≤ jointError M δ C := by
    dsimp [C,E,jointError]
    nlinarith [joint_scale_conversion K δ M hK hδ]
  have hη0 : 0 ≤ jointError M δ C := le_trans (by positivity) hη
  have hclose' : 6*E ≤ C*jointError M δ C := by
    calc
      _ ≤ 4*(53*E) := by linarith
      _ ≤ jointError M δ C := hη
      _ ≤ C*jointError M δ C := by
        simpa using mul_le_mul_of_nonneg_right hC hη0
  refine ⟨{
    measurement := fun j => (y j).measurement
    unitary := fun j => (y j).flip
    repairedQ := fun i => (y (sourceLabelEquiv M (.inl i))).datum
    conditional := ?_
    compulsory := ?_
    repaired_close := ?_
    relations := (exact_slots_triangular m.state (53*E) (by positivity) y hbounds).mono hη }⟩
  · intro i
    let j := sourceLabelEquiv M (.inl i)
    have hx : sourceSlots m M j=sourceConditionalSlot m i.val := by
      simp only [j,sourceSlots_label,sourceLabelSlot]
    have ht : (y j).ternary=true := (hkeep j).2.2.trans (congrArg RawSlot.ternary hx)
    have hF : (y j).flag=translate (sourceAt m 12) (sourceAt m 18) i.val :=
      (hkeep j).1.trans (congrArg RawSlot.flag hx)
    have hU : (y j).flip=translate (sourceAt m 12) (sourceAt m 22) i.val :=
      (hkeep j).2.1.trans (congrArg RawSlot.flip hx)
    obtain ⟨h3,h0,h1,h2⟩ := (y j).ternary_fields ht
    refine ⟨j,sourceLabel_conditional_val i,h3,?_,?_,h2,hU⟩
    · rw [h0,hF]; rfl
    · rw [h1,hF]; rfl
  · intro c i
    let j := sourceLabelEquiv M (.inr (c,i))
    have hx : sourceSlots m M j=sourceBinarySlot m c i.val := by
      simp only [j,sourceSlots_label,sourceLabelSlot]
    have ht : (y j).ternary=false := (hkeep j).2.2.trans (congrArg RawSlot.ternary hx)
    have hdata : (y j).datum=1-rawDigit (sourceClock m c) i.val :=
      (hbinary j (by rw [hx]; rfl)).trans (congrArg RawSlot.datum hx)
    have hU : (y j).flip=rawFlip (sourceClock m c) i.val :=
      (hkeep j).2.1.trans (congrArg RawSlot.flip hx)
    obtain ⟨h2,h0,h1⟩ := (y j).binary_fields ht
    refine ⟨j,sourceLabel_binary_val c i,h2,?_,?_,hU⟩
    · rw [h0,hdata]
      change 1-(1-rawDigit (sourceClock m c) i.val)=rawDigit (sourceClock m c) i.val
      abel
    · rw [h1,hdata]; rfl
  · intro i
    have h := hclose (sourceLabelEquiv M (.inl i))
    have he : weighted m.state ((y (sourceLabelEquiv M (.inl i))).datum-
        translate (sourceAt m 12) (sourceAt m 21) i.val) ≤ 6*E := by
      simpa only [sourceSlots_label,sourceLabelSlot,sourceConditionalSlot] using h
    exact he.trans hclose'

end
end E2
