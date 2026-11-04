import E2.FiniteSourceHalting
import E2.FiniteSourceCoordinates

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem sourceTuple_counter (p : CounterProgram) (N : ℕ) (i : Fin p.counters) (o : Fin 3) :
    Poly.eval (sourceTuple p N) (sv p (23+3*i.val+o.val)) =
      sourceDiagonal N (finiteSlots p N) (fun z => match o.val with
      | 0 => historyR p z.1.1.val z.2.1.val z.2.2.val i
      | 1 => historyZ p z.1.1.val z.2.1.val z.2.2.val i
      | _ => historyS p z.1.1.val z.2.1.val z.2.2.val i) := by
  have hi := i.isLt
  have ho := o.isLt
  have hs : 23+3*i.val+o.val<sourceSize p := by unfold sourceSize; omega
  have hc : ¬23+3*i.val+o.val<23 := by omega
  have hw : 23+3*i.val+o.val<23+3*p.counters := by omega
  have hd : (23+3*i.val+o.val-23)/3=i.val := by omega
  have hm : (23+3*i.val+o.val-23)%3=o.val := by omega
  simp only [sv,Poly.eval_var,sourceTuple,Fin.val_mk,Nat.mod_eq_of_lt hs,hc,hw,↓reduceDIte,hd,hm]
  have heta (h : i.val<p.counters) : (⟨i.val,h⟩:Fin p.counters)=i := Fin.ext rfl
  simp only [heta]
  fin_cases o <;> rfl

theorem sourceTuple_sr (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (sr p i)=sourceDiagonal N (finiteSlots p N)
      (fun z => historyR p z.1.1.val z.2.1.val z.2.2.val i) := by
  simpa only [sr,Fin.val_zero,Nat.add_zero] using sourceTuple_counter p N i 0

theorem sourceTuple_sz (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (sz p i)=sourceDiagonal N (finiteSlots p N)
      (fun z => historyZ p z.1.1.val z.2.1.val z.2.2.val i) := by
  simpa only [sz,show (1:Fin 3).val=1 from rfl,show 23+3*i.val+1=24+3*i.val by omega] using
    sourceTuple_counter p N i 1

theorem sourceTuple_ss (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N) (ss p i)=sourceDiagonal N (finiteSlots p N)
      (fun z => historyS p z.1.1.val z.2.1.val z.2.2.val i) := by
  simpa only [ss,show (2:Fin 3).val=2 from rfl,show 23+3*i.val+2=25+3*i.val by omega] using
    sourceTuple_counter p N i 2

theorem sourceTuple_sq (p : CounterProgram) (N : ℕ) (q : Fin p.controls) :
    Poly.eval (sourceTuple p N) (sq p q)=sourceDiagonal N (finiteSlots p N)
      (fun z => if q=(historyConfig p z.1.1.val z.2.1.val z.2.2.val).control then 1 else 0) := by
  have hq := q.isLt
  have hs : 23+3*p.counters+q.val<sourceSize p := by unfold sourceSize; omega
  have hc : ¬23+3*p.counters+q.val<23 := by omega
  have hw : ¬23+3*p.counters+q.val<23+3*p.counters := by omega
  have hd : 23+3*p.counters+q.val-(23+3*p.counters)=q.val := by omega
  simp only [sq,sv,Poly.eval_var,sourceTuple,Fin.val_mk,Nat.mod_eq_of_lt hs,hc,hw,↓reduceDIte,hd]

theorem source_zero_test_polynomial (p : CounterProgram) (N : ℕ) (i : Fin p.counters) :
    Poly.eval (sourceTuple p N)
      (sr p i-(sz p i+Poly.const (1/2)*(1-sz p i)*ss p i))=0 := by
  simp only [Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_const,Poly.eval_one,
    sourceTuple_sr,sourceTuple_sz,sourceTuple_ss,Matrix.smul_mul,Matrix.one_mul]
  rw [show (1:Mat (2^(3*N+finiteSlots p N)))=Matrix.diagonal (fun _ => 1) by simp]
  simp only [sourceDiagonal,Matrix.diagonal_sub,Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,
      smul_eq_mul,Matrix.zero_apply]
    have h := history_zero_test p (sourceBasisEquiv N (finiteSlots p N) a).1.1.val
      (sourceBasisEquiv N (finiteSlots p N) a).2.1.val
      (sourceBasisEquiv N (finiteSlots p N) a).2.2.val i
    have hC := congrArg (fun x : ℝ => (x:ℂ)) h
    push_cast at hC
    norm_num at hC ⊢
    linear_combination hC
  · simp [Matrix.diagonal_apply,hab]

theorem source_control_orthogonal (p : CounterProgram) (N : ℕ) (q q' : Fin p.controls) (h : q≠q') :
    Poly.eval (sourceTuple p N) (sq p q*sq p q')=0 := by
  rw [Poly.eval_mul,sourceTuple_sq,sourceTuple_sq]
  simp only [sourceDiagonal,Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.diagonal_apply_eq,Matrix.zero_apply]
    split_ifs with hq hq' hq'
    · exact False.elim (h (hq.trans hq'.symm))
    all_goals norm_num
  · simp [Matrix.diagonal_apply,hab]

theorem source_halt_flag_polynomial (p : CounterProgram) (N : ℕ) :
    Poly.eval (sourceTuple p N) ((1-sv p 18)*sq p p.halt)=0 := by
  rw [Poly.eval_mul,Poly.eval_sub,Poly.eval_one,sourceTuple_core p N 18 (by omega),sourceTuple_sq]
  change (1-sourceDiagonal N (finiteSlots p N) (fun z => optionalFlag (wordMask p N) z.1))*_ = 0
  rw [show (1:Mat (2^(3*N+finiteSlots p N)))=Matrix.diagonal (fun _ => 1) by simp]
  simp only [sourceDiagonal,Matrix.diagonal_sub,Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.diagonal_apply_eq,Matrix.zero_apply]
    by_cases hh : p.halt=(historyConfig p (sourceBasisEquiv N (finiteSlots p N) a).1.1.val
        (sourceBasisEquiv N (finiteSlots p N) a).2.1.val
        (sourceBasisEquiv N (finiteSlots p N) a).2.2.val).control
    · have hf := sourceHistory_halt_flag p N (sourceBasisEquiv N (finiteSlots p N) a).1.1
        (sourceBasisEquiv N (finiteSlots p N) a).2.1 (sourceBasisEquiv N (finiteSlots p N) a).2.2 hh.symm
      simp [hh,optionalFlag,hf]
    · simp [hh]
  · simp [Matrix.diagonal_apply,hab]

theorem eval_psum_matrix {ι : Type*} {d : ℕ} (v : ι → Mat d) (xs : List (Poly ι)) :
    Poly.eval v (psum xs)=(xs.map (Poly.eval v)).sum := by
  induction xs with
  | nil => simp [psum]
  | cons x xs ih =>
    simpa only [psum,List.foldr_cons,Poly.eval_add,List.map_cons,List.sum_cons] using
      (congrArg (fun a => Poly.eval v x+a) ih)

theorem sum_finRange_matrix {d : ℕ} (n : ℕ) (f : Fin n → Mat d) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem source_control_partition (p : CounterProgram) (N : ℕ) :
    Poly.eval (sourceTuple p N) (psum ((List.finRange p.controls).map (sq p))-1)=0 := by
  rw [Poly.eval_sub,Poly.eval_one,eval_psum_matrix,List.map_map]
  simp only [Function.comp_def,sourceTuple_sq]
  rw [sum_finRange_matrix]
  apply sub_eq_zero.mpr
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [Matrix.sum_apply,sourceDiagonal,Matrix.diagonal_apply_eq,Matrix.one_apply_eq,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero]
    simp
  · simp [sourceDiagonal,Matrix.sum_apply,Matrix.diagonal_apply,hab]
end
end E2.FiniteConstruction