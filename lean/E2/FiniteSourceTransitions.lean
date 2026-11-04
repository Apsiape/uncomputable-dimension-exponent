import E2.FiniteProgramEvaluation

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false

def scalarCounterTerm (p : CounterProgram) (c : Configuration p)
    (r z : Fin p.counters → ℝ) (i : Fin p.counters) (q : Fin p.controls) : ℝ :=
  let a : ℝ := if q=c.control then 1 else 0
  match p.instruction q with
  | .inc j _ => a*((if i=j then 1/2 else 1)*r i)
  | .dec j _ _ => a*z j*r i+a*(1-z j)*((if i=j then 2 else 1)*r i)
  | .jump _ => a*r i
  | .stay => a*r i

def scalarControlTerm (p : CounterProgram) (c : Configuration p)
    (z : Fin p.counters → ℝ) (i q : Fin p.controls) : ℝ :=
  let a : ℝ := if q=c.control then 1 else 0
  match p.instruction q with
  | .inc _ q' => if q'=i then a else 0
  | .dec j q₀ q₁ => (if q₀=i then a*z j else 0)+(if q₁=i then a*(1-z j) else 0)
  | .jump q' => if q'=i then a else 0
  | .stay => if q=i then a else 0

theorem scalarCounterTerm_inactive (p : CounterProgram) (c : Configuration p)
    (r z : Fin p.counters → ℝ) (i : Fin p.counters) (q : Fin p.controls) (h : q≠c.control) :
    scalarCounterTerm p c r z i q=0 := by
  cases hi : p.instruction q <;> simp [scalarCounterTerm,hi,h]

theorem scalarControlTerm_inactive (p : CounterProgram) (c : Configuration p)
    (z : Fin p.counters → ℝ) (i q : Fin p.controls) (h : q≠c.control) :
    scalarControlTerm p c z i q=0 := by
  cases hi : p.instruction q <;> simp [scalarControlTerm,hi,h]

theorem scalarCounterTerm_active (p : CounterProgram) (c : Configuration p) (i : Fin p.counters) :
    scalarCounterTerm p c (fun j => counterCoordinate (c.counter j))
      (fun j => counterZero (c.counter j)) i c.control=counterCoordinate ((p.step c).counter i) := by
  cases h : p.instruction c.control with
  | inc j q => by_cases hi : i=j <;>
      simp [scalarCounterTerm,h,CounterProgram.step,hi,eq_comm,Function.update_apply,counterCoordinate_succ]
  | dec j q₀ q₁ =>
    by_cases hn : c.counter j=0
    · simp [scalarCounterTerm,h,CounterProgram.step,counterZero,hn]
    · by_cases hi : i=j <;>
        simp [scalarCounterTerm,h,CounterProgram.step,counterZero,hn,hi,eq_comm,
          Function.update_apply,counterCoordinate_pred hn]
  | jump q => simp [scalarCounterTerm,h,CounterProgram.step]
  | stay => simp [scalarCounterTerm,h,CounterProgram.step]

theorem scalarControlTerm_active (p : CounterProgram) (c : Configuration p) (i : Fin p.controls) :
    scalarControlTerm p c (fun j => counterZero (c.counter j)) i c.control =
      if i=(p.step c).control then 1 else 0 := by
  cases h : p.instruction c.control <;>
    simp [scalarControlTerm,h,CounterProgram.step,counterZero,eq_comm]
  all_goals (try split_ifs) <;> simp_all

theorem source_nextCounter (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (nextCounter p i)=sourceDiagonal N (finiteSlots p N)
      (fun b => ∑ q, scalarCounterTerm p (historyConfig p b.1.1.val b.2.1.val b.2.2.val)
        (historyR p b.1.1.val b.2.1.val b.2.2.val)
        (historyZ p b.1.1.val b.2.1.val b.2.2.val) i q) := by
  rw [ProgramEvaluation.eval_nextCounter]
  have ht (q : Fin p.controls) : ProgramEvaluation.counterTerm p (sourceTuple p N) i q =
      sourceDiagonal N (finiteSlots p N) (fun b => scalarCounterTerm p
        (historyConfig p b.1.1.val b.2.1.val b.2.2.val)
        (historyR p b.1.1.val b.2.1.val b.2.2.val)
        (historyZ p b.1.1.val b.2.1.val b.2.2.val) i q) := by
    cases h : p.instruction q <;>
      simp only [ProgramEvaluation.counterTerm,h,sourceTuple_sr,sourceTuple_sz,sourceTuple_sq]
    all_goals
      (try split_ifs) <;> ext a b <;> by_cases hab : a=b
    all_goals
      simp [sourceDiagonal,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply,
        Matrix.smul_apply,smul_eq_mul,scalarCounterTerm,h,hab, *]
    all_goals
      (try split_ifs) <;> simp_all [scalarCounterTerm,scalarControlTerm] <;> push_cast <;> ring
  simp only [ht]
  ext a b
  by_cases hab : a=b <;> simp [sourceDiagonal,Matrix.sum_apply,Matrix.diagonal_apply,hab]

theorem source_nextControl (p : CounterProgram) (N : ℕ) (i : Fin p.controls) :
    Poly.eval (sourceTuple p N) (nextControl p i)=sourceDiagonal N (finiteSlots p N)
      (fun b => ∑ q, scalarControlTerm p (historyConfig p b.1.1.val b.2.1.val b.2.2.val)
        (historyZ p b.1.1.val b.2.1.val b.2.2.val) i q) := by
  rw [ProgramEvaluation.eval_nextControl]
  have ht (q : Fin p.controls) : ProgramEvaluation.controlTerm p (sourceTuple p N) i q =
      sourceDiagonal N (finiteSlots p N) (fun b => scalarControlTerm p
        (historyConfig p b.1.1.val b.2.1.val b.2.2.val)
        (historyZ p b.1.1.val b.2.1.val b.2.2.val) i q) := by
    cases h : p.instruction q <;>
      simp only [ProgramEvaluation.controlTerm,h,sourceTuple_sq,sourceTuple_sz]
    all_goals
      (try split_ifs) <;> ext a b <;> by_cases hab : a=b
    all_goals
      simp [sourceDiagonal,Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply,
        Matrix.smul_apply,smul_eq_mul,scalarControlTerm,h,hab, *]
    all_goals
      (try split_ifs) <;> simp_all [scalarCounterTerm,scalarControlTerm] <;> push_cast <;> ring
  simp only [ht]
  ext a b
  by_cases hab : a=b <;> simp [sourceDiagonal,Matrix.sum_apply,Matrix.diagonal_apply,hab]

end
end E2.FiniteConstruction
