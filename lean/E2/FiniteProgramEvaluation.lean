import E2.FiniteSourceInitialization

namespace E2.FiniteConstruction.ProgramEvaluation
noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {d : ℕ}

theorem eval_psum {ι : Type*} (x : ι → Mat d) (rs : List (Poly ι)) :
    (psum rs).eval x=(rs.map (Poly.eval x)).sum := by
  induction rs with
  | nil => simp [psum]
  | cons r rs ih => simpa only [psum,List.foldr_cons,Poly.eval_add,List.map_cons,List.sum_cons] using congrArg (fun y => r.eval x+y) ih

theorem sum_finRange {B : Type*} [AddCommMonoid B] (n : ℕ) (f : Fin n → B) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem sum_flatMap {B C : Type*} [AddMonoid B] (xs : List C) (f : C → List B) :
    (xs.flatMap f).sum=(xs.map (fun c => (f c).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

def counterTerm (p : CounterProgram) (x : SourceVar p → Mat d) (i : Fin p.counters) (q : Fin p.controls) : Mat d :=
  match p.instruction q with
  | .inc j _ => (sq p q).eval x * ((if i=j then 1/2 else 1:ℂ) • (sr p i).eval x)
  | .dec j _ _ => (sq p q).eval x*(sz p j).eval x*(sr p i).eval x +
      (sq p q).eval x*(1-(sz p j).eval x)*((if i=j then 2 else 1:ℂ) • (sr p i).eval x)
  | .jump _ => (sq p q).eval x*(sr p i).eval x
  | .stay => (sq p q).eval x*(sr p i).eval x

def controlTerm (p : CounterProgram) (x : SourceVar p → Mat d) (i q : Fin p.controls) : Mat d :=
  match p.instruction q with
  | .inc _ q' => if q'=i then (sq p q).eval x else 0
  | .dec j q₀ q₁ => (if q₀=i then (sq p q).eval x*(sz p j).eval x else 0) +
      (if q₁=i then (sq p q).eval x*(1-(sz p j).eval x) else 0)
  | .jump q' => if q'=i then (sq p q).eval x else 0
  | .stay => if q=i then (sq p q).eval x else 0

theorem eval_nextCounter (p : CounterProgram) (x : SourceVar p → Mat d) (i : Fin p.counters) :
    (nextCounter p i).eval x=∑ q, counterTerm p x i q := by
  rw [nextCounter,eval_psum,programBranches,List.map_flatMap,List.map_flatMap,sum_flatMap]
  rw [←sum_finRange]
  congr 1
  apply List.map_congr_left
  intro q hq
  cases h : p.instruction q <;>
    simp [counterTerm,h,Poly.eval_sub,smul_mul_assoc,one_mul,mul_smul_comm,mul_assoc]
  all_goals split_ifs <;> norm_num

theorem eval_nextControl (p : CounterProgram) (x : SourceVar p → Mat d) (i : Fin p.controls) :
    (nextControl p i).eval x=∑ q, controlTerm p x i q := by
  rw [nextControl,eval_psum,programBranches,List.map_flatMap,List.map_flatMap,sum_flatMap]
  rw [←sum_finRange]
  congr 1
  apply List.map_congr_left
  intro q hq
  cases h : p.instruction q <;> simp [controlTerm,h]
  all_goals split_ifs <;> simp

end
end E2.FiniteConstruction.ProgramEvaluation
