import E2.FiniteSourceTransitions

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

theorem history_counter_next (p : CounterProgram) (N : ℕ) (b q t : BinaryWord N) (i : Fin p.counters) :
    historyR p b.val q.val (incrementWord N t).val i =
      if listReset q.val (incrementWord N t).val then (if i.val=0 then decodedR b.val else 1)
      else ∑ j, scalarCounterTerm p (historyConfig p b.val q.val t.val)
        (historyR p b.val q.val t.val) (historyZ p b.val q.val t.val) i j := by
  cases hr : listReset q.val (incrementWord N t).val
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [Finset.sum_eq_single (historyConfig p b.val q.val t.val).control]
    · cases hd : binaryDecode b.val with
      | none =>
        have hi := historyInitial_idle p b.val (by simp [decodedL,hd])
          (listNumber t.val % 2^leadingOnes q.val)
        change (historyConfig p b.val q.val t.val).control=p.idle at hi
        have hs : p.step (historyConfig p b.val q.val t.val)=historyConfig p b.val q.val t.val := by
          simp [CounterProgram.step,hi,p.idle_absorbing]
        have ht := sourceHistory_transition p N b q t
        simp only [hr,Bool.false_eq_true,↓reduceIte,hs] at ht
        simp [scalarCounterTerm,hi,p.idle_absorbing,historyR,ht]
      | some z =>
        have ht := sourceHistory_transition p N b q t
        simp only [hr,Bool.false_eq_true,↓reduceIte] at ht
        have hR : historyR p b.val q.val t.val = (fun j => counterCoordinate ((historyConfig p b.val q.val t.val).counter j)) := by
          funext j; simp [historyR,hd]
        have hZ : historyZ p b.val q.val t.val = (fun j => counterZero ((historyConfig p b.val q.val t.val).counter j)) := by
          funext j; simp [historyZ,hd]
        rw [hR,hZ]
        simp only [historyR,hd,Option.some_ne_none,false_and,ite_false,ht]
        exact (scalarCounterTerm_active p (historyConfig p b.val q.val t.val) i).symm
    · intro j hj hne
      exact scalarCounterTerm_inactive p _ _ _ i j hne
    · simp
  · simp only [↓reduceIte]
    exact historyR_initial p N b q (incrementWord N t) hr i

theorem history_control_next (p : CounterProgram) (N : ℕ) (b q t : BinaryWord N) (i : Fin p.controls) :
    (if i=(historyConfig p b.val q.val (incrementWord N t).val).control then (1:ℝ) else 0) =
      if listReset q.val (incrementWord N t).val then
        (if i=p.start then boolValue (decodedL b.val)
          else if i=p.idle then 1-boolValue (decodedL b.val) else 0)
      else ∑ j, scalarControlTerm p (historyConfig p b.val q.val t.val)
        (historyZ p b.val q.val t.val) i j := by
  cases hr : listReset q.val (incrementWord N t).val
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [Finset.sum_eq_single (historyConfig p b.val q.val t.val).control]
    · have ht := sourceHistory_transition p N b q t
      simp only [hr,Bool.false_eq_true,↓reduceIte] at ht
      rw [ht]
      cases hd : binaryDecode b.val with
      | none =>
        have hi := historyInitial_idle p b.val (by simp [decodedL,hd])
          (listNumber t.val % 2^leadingOnes q.val)
        change (historyConfig p b.val q.val t.val).control=p.idle at hi
        simp [scalarControlTerm,CounterProgram.step,hi,p.idle_absorbing,eq_comm]
      | some z =>
        have hZ : historyZ p b.val q.val t.val = (fun j => counterZero ((historyConfig p b.val q.val t.val).counter j)) := by
          funext j; simp [historyZ,hd]
        rw [hZ]
        exact (scalarControlTerm_active p (historyConfig p b.val q.val t.val) i).symm
    · intro j hj hne
      exact scalarControlTerm_inactive p _ _ i j hne
    · simp
  · simp only [↓reduceIte]
    exact historyQ_initial p N b q (incrementWord N t) hr i

theorem source_timeStep_diagonal (p : CounterProgram) (N : ℕ)
    (v : SourceBasis N (finiteSlots p N) → ℝ) :
    (sourceCore p N 13).conjTranspose*sourceDiagonal N (finiteSlots p N) v*sourceCore p N 13 =
      sourceDiagonal N (finiteSlots p N)
        (fun z => v (z.1,(z.2.1,incrementWord N z.2.2))) := by
  have hc := sourceConj_diagonal N (finiteSlots p N) (timeLift (incrementWord N)) v
  have hs : (timeLift (k := finiteSlots p N) (incrementWord N)).symm =
      timeLift (incrementWord N).symm := by
    apply Equiv.ext
    intro z
    rfl
  have he : (sourcePerm N (finiteSlots p N) (timeLift (incrementWord N)))⁻¹ =
      sourcePerm N (finiteSlots p N) (timeLift (incrementWord N).symm) := by
    change (sourcePerm N (finiteSlots p N) (timeLift (incrementWord N))).symm = _
    rw [sourcePerm_symm,hs]
  change ((sourcePerm N (finiteSlots p N) (timeLift (incrementWord N).symm)).permMatrix ℂ).conjTranspose*
    sourceDiagonal N (finiteSlots p N) v*
    (sourcePerm N (finiteSlots p N) (timeLift (incrementWord N).symm)).permMatrix ℂ = _
  rw [←he,Matrix.conjTranspose_permMatrix,inv_inv]
  have hr : (fun z : SourceBasis N (finiteSlots p N) => v (timeLift (incrementWord N) z)) =
      (fun z => v (z.1,(z.2.1,incrementWord N z.2.2))) := by
    funext z
    rcases z with ⟨a,q,t⟩
    rfl
  rw [hr] at hc
  simpa only [Matrix.conjTranspose_permMatrix] using hc

theorem source_counter_transition (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N)
      (conjP (sv p 13).adj (sr p i) -
        (conjP (sv p 13).adj (sv p 17)*initialCounter p i+
          (1-conjP (sv p 13).adj (sv p 17))*nextCounter p i))=0 := by
  simp only [conjP,Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_adj,Poly.eval_one,
    sourceTuple_core p N 13 (by omega),sourceTuple_core p N 17 (by omega),
    Matrix.conjTranspose_conjTranspose,sourceTuple_sr,source_initialCounter,source_nextCounter]
  change _-( ((sourceCore p N 13).conjTranspose*sourceDiagonal N (finiteSlots p N)
    (fun z => boolValue (listReset z.2.1.val z.2.2.val))*sourceCore p N 13)*_+
    (1-(sourceCore p N 13).conjTranspose*sourceDiagonal N (finiteSlots p N)
      (fun z => boolValue (listReset z.2.1.val z.2.2.val))*sourceCore p N 13)*_)=0
  apply sub_eq_zero.mpr
  simp only [source_timeStep_diagonal,sourceDiagonal_one_sub,sourceDiagonal_mul,sourceDiagonal_add]
  congr 1
  funext z
  rw [history_counter_next p N z.1.1 z.2.1 z.2.2 i]
  cases hr : listReset z.2.1.val (incrementWord N z.2.2).val <;> simp [boolValue,hr]

theorem source_control_transition (p : CounterProgram) (N : ℕ) (i : Fin p.controls) :
    Poly.eval (sourceTuple p N)
      (conjP (sv p 13).adj (sq p i) -
        (conjP (sv p 13).adj (sv p 17)*initialControl p i+
          (1-conjP (sv p 13).adj (sv p 17))*nextControl p i))=0 := by
  simp only [conjP,Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_adj,Poly.eval_one,
    sourceTuple_core p N 13 (by omega),sourceTuple_core p N 17 (by omega),
    Matrix.conjTranspose_conjTranspose,sourceTuple_sq,source_initialControl,source_nextControl]
  change _-( ((sourceCore p N 13).conjTranspose*sourceDiagonal N (finiteSlots p N)
    (fun z => boolValue (listReset z.2.1.val z.2.2.val))*sourceCore p N 13)*_+
    (1-(sourceCore p N 13).conjTranspose*sourceDiagonal N (finiteSlots p N)
      (fun z => boolValue (listReset z.2.1.val z.2.2.val))*sourceCore p N 13)*_)=0
  apply sub_eq_zero.mpr
  simp only [source_timeStep_diagonal,sourceDiagonal_one_sub,sourceDiagonal_mul,sourceDiagonal_add]
  congr 1
  funext z
  rw [history_control_next p N z.1.1 z.2.1 z.2.2 i]
  cases hr : listReset z.2.1.val (incrementWord N z.2.2).val <;> simp [boolValue,hr]

end
end E2.FiniteConstruction
