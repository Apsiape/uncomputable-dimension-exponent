import E2.FiniteSourceWorkspace
import E2.FiniteSourceDiagonal

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem historyR_initial (p : CounterProgram) (N : ℕ) (b q t : BinaryWord N)
    (hr : listReset q.val t.val=true) (i : Fin p.counters) :
    historyR p b.val q.val t.val i = if i.val=0 then decodedR b.val else 1 := by
  unfold historyR
  rw [sourceHistory_initial p N b q t hr]
  simp only [historyInitial,CounterProgram.initial]
  cases hd : binaryDecode b.val with
  | none => by_cases hi : i.val=0 <;> simp [hd,hi,decodedR,counterCoordinate]
  | some z => by_cases hi : i.val=0 <;> simp [hd,hi,decodedR,counterCoordinate]

theorem historyQ_initial (p : CounterProgram) (N : ℕ) (b q t : BinaryWord N)
    (hr : listReset q.val t.val=true) (j : Fin p.controls) :
    (if j=(historyConfig p b.val q.val t.val).control then (1:ℝ) else 0) =
      if j=p.start then boolValue (decodedL b.val)
      else if j=p.idle then 1-boolValue (decodedL b.val) else 0 := by
  rw [sourceHistory_initial p N b q t hr]
  change (if j=(if decodedL b.val then p.start else p.idle) then (1:ℝ) else 0)=_
  cases h : decodedL b.val <;> by_cases hs : j=p.start <;>
    by_cases hi : j=p.idle <;> simp_all [boolValue,p.distinct.1,Ne.symm p.distinct.1]

theorem source_initialCounter (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (initialCounter p i)=
      sourceDiagonal N (finiteSlots p N) (fun z => if i.val=0 then decodedR z.1.1.val else 1) := by
  unfold initialCounter
  split_ifs
  · exact sourceTuple_core p N 16 (by omega)
  · simp only [Poly.eval_one,sourceDiagonal_one]

theorem source_initialControl (p : CounterProgram) (N : ℕ) (j : Fin p.controls) :
    Poly.eval (sourceTuple p N) (initialControl p j)=
      sourceDiagonal N (finiteSlots p N) (fun z =>
        if j=p.start then boolValue (decodedL z.1.1.val)
        else if j=p.idle then 1-boolValue (decodedL z.1.1.val) else 0) := by
  unfold initialControl
  split_ifs
  · exact sourceTuple_core p N 15 (by omega)
  · rw [Poly.eval_sub,Poly.eval_one,sourceTuple_core p N 15 (by omega)]
    exact sourceDiagonal_one_sub _ _ _
  · simp [Poly.eval_zero,sourceDiagonal]

theorem source_counter_initialization (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (sv p 17*sr p i-sv p 17*initialCounter p i)=0 := by
  simp only [Poly.eval_sub,Poly.eval_mul,sourceTuple_sr,source_initialCounter,
    sourceTuple_core p N 17 (by omega)]
  change sourceDiagonal N (finiteSlots p N) (fun z => boolValue (listReset z.2.1.val z.2.2.val))*_ -
    sourceDiagonal N (finiteSlots p N) (fun z => boolValue (listReset z.2.1.val z.2.2.val))*_=0
  apply sub_eq_zero.mpr
  rw [sourceDiagonal_mul,sourceDiagonal_mul]
  congr 1
  funext z
  cases hr : listReset z.2.1.val z.2.2.val
  · simp [hr,boolValue]
  · rw [historyR_initial p N z.1.1 z.2.1 z.2.2 hr]

theorem source_control_initialization (p : CounterProgram) (N : ℕ) (j : Fin p.controls) :
    Poly.eval (sourceTuple p N) (sv p 17*sq p j-sv p 17*initialControl p j)=0 := by
  simp only [Poly.eval_sub,Poly.eval_mul,sourceTuple_sq,source_initialControl,
    sourceTuple_core p N 17 (by omega)]
  change sourceDiagonal N (finiteSlots p N) (fun z => boolValue (listReset z.2.1.val z.2.2.val))*_ -
    sourceDiagonal N (finiteSlots p N) (fun z => boolValue (listReset z.2.1.val z.2.2.val))*_=0
  apply sub_eq_zero.mpr
  rw [sourceDiagonal_mul,sourceDiagonal_mul]
  congr 1
  funext z
  cases hr : listReset z.2.1.val z.2.2.val
  · simp [hr,boolValue]
  · rw [historyQ_initial p N z.1.1 z.2.1 z.2.2 hr]

end
end E2.FiniteConstruction
