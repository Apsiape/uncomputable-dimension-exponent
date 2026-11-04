import E2.Joint

namespace E2
noncomputable section
open scoped BigOperators

theorem JointFamily.conditional_kind {p : CounterProgram} {d M : ℕ} {δ C : ℝ}
    {m : Model (sourcePresentation p) d δ} (r : JointFamily m M C) (i : Fin M) :
    (r.measurement (sourceLabelEquiv M (.inl i))).outcomes=3 ∧
      (r.measurement (sourceLabelEquiv M (.inl i))).active=
        translate (modelValue m 12) (modelValue m 18) i.val := by
  obtain ⟨j,hj,hout,h0,_h1,_h2,_hu⟩ := r.conditional i
  have he : j=sourceLabelEquiv M (.inl i) := Fin.ext hj
  subst j
  refine ⟨hout,?_⟩
  rw [Measurement.active,hout,if_pos rfl,h0]
  abel

theorem JointFamily.binary_kind {p : CounterProgram} {d M : ℕ} {δ C : ℝ}
    {m : Model (sourcePresentation p) d δ} (r : JointFamily m M C) (c : Fin 3) (i : Fin M) :
    (r.measurement (sourceLabelEquiv M (.inr (c,i)))).outcomes=2 := by
  obtain ⟨j,hj,hout,_⟩ := r.compulsory c i
  have he : j=sourceLabelEquiv M (.inr (c,i)) :=
    Fin.ext (hj.trans (sourceLabel_binary_val c i).symm)
  subst j; exact hout

/-- The 3M compulsory measurements contribute exactly 3M binary bits. -/
theorem JointFamily.binary_count {p : CounterProgram} {d M : ℕ} {δ C : ℝ}
    {m : Model (sourcePresentation p) d δ} (r : JointFamily m M C) :
    binaryCount r.measurement=3*M := by
  classical
  unfold binaryCount
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [←(sourceLabelEquiv M).sum_comp (fun j => if (r.measurement j).outcomes=2 then (1:ℕ) else 0)]
  rw [Fintype.sum_sum_type]
  have h1 (i : Fin M) := (r.conditional_kind i).1
  have h2 (a : Fin 3 × Fin M) := r.binary_kind a.1 a.2
  simp only [h1,h2,show (3:ℕ) ≠ 2 by decide,ite_false,ite_true]
  simp

/-- The repaired data do not change activation: only the raw flags enter the count. -/
theorem JointFamily.active_sum {p : CounterProgram} {d M : ℕ} {δ C : ℝ}
    {m : Model (sourcePresentation p) d δ} (r : JointFamily m M C) :
    activeSum m.state r.measurement=
      ∑ i : Fin M, expectation m.state (translate (modelValue m 12) (modelValue m 18) i.val) := by
  classical
  unfold activeSum
  rw [Finset.sum_filter]
  rw [←(sourceLabelEquiv M).sum_comp (fun j => if (r.measurement j).outcomes=3 then
    expectation m.state (r.measurement j).active else 0)]
  rw [Fintype.sum_sum_type]
  have h1 (i : Fin M) := (r.conditional_kind i).1
  have h2 (a : Fin 3 × Fin M) := r.binary_kind a.1 a.2
  have h3 (i : Fin M) := (r.conditional_kind i).2
  simp only [h1,h2,h3,show (2:ℕ) ≠ 3 by decide,ite_true,ite_false,Finset.sum_const_zero,add_zero]

end
end E2
