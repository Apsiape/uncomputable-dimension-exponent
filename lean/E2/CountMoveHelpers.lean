import E2.CountPathIntertwining
import E2.CountDecoder

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

 theorem finRange_erase {n : ℕ} (i : Fin (n+1)) :
    ((List.finRange (n+1)).filter (fun j => j≠i)) = (List.finRange n).map i.succAbove := by
  induction n with
  | zero =>
    have hi : i=0 := Fin.ext (by have := i.isLt; omega)
    subst i
    decide
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [List.finRange_succ]
      simp [List.filter_map, Function.comp_def]
    · have hzero : decide ((0:Fin (n+2))≠j.succ)=true := decide_eq_true (Ne.symm (Fin.succ_ne_zero j))
      have hpred : (fun x : Fin (n+1) => decide (x.succ≠j.succ)) = (fun x => decide (x≠j)) := by
        funext x
        simp only [ne_eq, Fin.succ_inj]
      rw [List.finRange_succ, List.filter_cons, hzero]
      simp only [ite_true]
      rw [List.filter_map]
      change 0 :: ((List.finRange (n+1)).filter (fun x => decide (x.succ≠j.succ))).map Fin.succ = _
      rw [hpred, ih j, List.finRange_succ]
      simp only [List.map_cons, Fin.succ_succAbove_zero, List.map_map, Function.comp_def, Fin.succ_succAbove_succ]
 def erasedWord {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m) (a : RecordType p) : Mat d :=
    (((List.finRange m).filter (fun j => j≠i)).map (fun j => (p j).projection (a j))).prod

 theorem erased_word_reindex {d n : ℕ} (p : Fin (n+1) → Measurement d) (i : Fin (n+1)) (a : RecordType p) :
    erasedWord p i a = reverseWord (fun j => p (i.succAbove j)) (fun j => a (i.succAbove j)) := by
  simp only [erasedWord, finRange_erase, List.map_map, reverseWord, List.ofFn_eq_map, Function.comp_def]

 theorem erased_word_cons_zero {d n : ℕ} (p : Fin (n+1) → Measurement d)
    (b : Fin (p 0).outcomes) (a : RecordType (fun j => p j.succ)) :
    erasedWord p 0 (Fin.cons b a)=reverseWord (fun j => p j.succ) a := by
  rw [erased_word_reindex]
  simp only [Fin.zero_succAbove, Fin.cons_succ]

 theorem erased_word_cons_succ {d n : ℕ} (p : Fin (n+1) → Measurement d) (i : Fin n)
    (b : Fin (p 0).outcomes) (a : RecordType (fun j => p j.succ)) :
    erasedWord p i.succ (Fin.cons b a)=(p 0).projection b*erasedWord (fun j => p j.succ) i a := by
  have hz : (0:Fin (n+1))≠i.succ := Ne.symm (Fin.succ_ne_zero _)
  unfold erasedWord
  rw [List.finRange_succ]
  simp [List.filter_map, Function.comp_def, hz]

 theorem sum_records_pivot {d n : ℕ} (p : Fin (n+1) → Measurement d) (i : Fin (n+1))
    {B : Type*} [AddCommMonoid B] (f : RecordType p → B) :
    (∑ a, f a)=∑ b : Fin (p i).outcomes, ∑ a : RecordType (fun j => p (i.succAbove j)), f (i.insertNth b a) := by
  calc
    _ = ∑ t : Fin (p i).outcomes × RecordType (fun j => p (i.succAbove j)), f (i.insertNth t.1 t.2) :=
      (Fintype.sum_equiv (Fin.insertNthEquiv (fun j => Fin (p j).outcomes) i) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

end
end E2




