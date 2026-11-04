import E2.CompilerPackingRealize

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

section Packing
variable {κ A : Type*} [Ring A] [Algebra ℚ A]

def word (x : κ → A) (w : List κ) : A := (w.map x).prod

def linearSum (x : κ → A) (ws : CompilerWords.WordSum κ) : A :=
  (ws.map (fun t => t.1 • word x t.2)).sum

def signedWord (x : κ → A) (t : Bool × List κ) : A :=
  if t.1 then word x t.2 else -word x t.2

omit [Algebra ℚ A] in
theorem flat_sum {α : Type*} (l : List α) (f : α → List A) :
    (l.flatMap f).sum = (l.map (fun t => (f t).sum)).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

omit [Algebra ℚ A] in
theorem flat_prod {α : Type*} (l : List α) (f : α → List A) :
    (l.flatMap f).prod = (l.map (fun t => (f t).prod)).prod := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.flatMap_cons,List.prod_append,List.map_cons,List.prod_cons,ih]

theorem signed_multiplicity (z : ℤ) (w : A) :
    (2*z.natAbs) • (if decide (0 ≤ z) then w else -w) = (2*(z:ℚ)) • w := by
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  by_cases h : 0 ≤ z
  · simp only [h,decide_true,↓reduceIte,Nat.cast_mul,Nat.cast_ofNat]
    congr 1
    have hz : (z.natAbs:ℚ) = (z:ℚ) := by rw [Nat.cast_natAbs,abs_of_nonneg h]
    rw [hz]
  · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte,smul_neg,Nat.cast_mul,Nat.cast_ofNat]
    rw [← neg_smul]
    congr 1
    have hz : (z.natAbs:ℚ) = -(z:ℚ) := by
      rw [Nat.cast_natAbs,abs_of_neg (lt_of_not_ge h),Int.cast_neg]
    rw [hz]
    ring

theorem signedWords_sum (x : κ → A) (ws : CompilerWords.WordSum κ) :
    ((signedWords ws).map (signedWord x)).sum =
      (2*(denominator ws:ℚ)) • linearSum x ws := by
  unfold signedWords
  rw [List.map_flatMap,flat_sum]
  simp only [List.map_replicate,List.sum_replicate,signedWord]
  simp_rw [signed_multiplicity]
  rw [linearSum,List.smul_sum]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [denominator_clears ws t ht,smul_smul]
  congr 1
  ring

theorem packedWords_sum (x : κ → A) (ws : CompilerWords.WordSum κ) :
    ((packedWords ws).map (signedWord x)).sum =
      (2*(denominator ws:ℚ)) • linearSum x ws := by
  simp only [packedWords,List.map_append,List.sum_append,List.map_replicate,List.sum_replicate]
  rw [signedWords_sum]
  simp [signedWord,word]

theorem letters_block (x : κ → A) (ws : CompilerWords.WordSum κ)
    (a : Fin (selectorCount ws) → Bool) :
    ((letters ws).map (fun t => if a=t.selector then
      (if t.positive then t.source.elim 1 x else -(t.source.elim 1 x)) else 1)).prod =
      signedWord x ((packedWords ws).getD (Fintype.equivFin _ a).val (true,[])) := by
  classical
  unfold letters
  rw [List.map_flatMap,flat_prod]
  have he (b : Fin (selectorCount ws) → Bool) :
      ((let t := (packedWords ws).getD (Fintype.equivFin _ b).val (true,[])
        (⟨b,none,t.1⟩ : Letter κ (selectorCount ws)) :: t.2.map (fun s => ⟨b,some s,true⟩)).map
        (fun t => if a=t.selector then
          (if t.positive then t.source.elim 1 x else -(t.source.elim 1 x)) else 1)).prod =
      if a=b then signedWord x ((packedWords ws).getD (Fintype.equivFin _ b).val (true,[])) else 1 := by
    by_cases h : a=b
    · subst b
      simp only [List.map_cons,List.prod_cons,List.map_map,Function.comp_def,↓reduceIte,
        Option.elim_none,Option.elim_some]
      generalize (packedWords ws).getD (Fintype.equivFin _ a).val (true,[]) = t
      rcases t with ⟨b,w⟩
      cases b <;> simp [signedWord,word]
    · simp [h,Function.comp_def]
  simp_rw [he]
  rw [List.prod_map_eq_pow_single a _ (by intro b hb _; simp [Ne.symm hb])]
  simp [List.Nodup.count (Finset.nodup_toList _)]

theorem packed_selector_sum (x : κ → A) (ws : CompilerWords.WordSum κ) :
    (∑ a : Fin (selectorCount ws) → Bool,
      signedWord x ((packedWords ws).getD (Fintype.equivFin _ a).val (true,[]))) =
      (2*(denominator ws:ℚ)) • linearSum x ws := by
  classical
  have hc : Fintype.card (Fin (selectorCount ws) → Bool) = (packedWords ws).length := by
    simp [packed_length]
  let e : (Fin (selectorCount ws) → Bool) ≃ Fin (packedWords ws).length :=
    (Fintype.equivFin _).trans (finCongr hc)
  calc
    _ = ∑ i : Fin (packedWords ws).length, signedWord x ((packedWords ws).get i) := by
      apply Fintype.sum_equiv e
      intro a
      congr 1
      exact List.getD_eq_getElem _ _ (by simpa [← hc] using (Fintype.equivFin _ a).isLt)
    _ = ((packedWords ws).map (signedWord x)).sum := by
      conv_rhs => rw [← List.ofFn_get (packedWords ws),List.map_ofFn,List.sum_ofFn]
      rfl
    _ = _ := packedWords_sum x ws
end Packing

end
end E2.CompilerNetwork

