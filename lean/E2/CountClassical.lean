import E2.CountClassicalChain

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 500000

 theorem head_entropy_lower {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d) :
    (if (p 0).outcomes=2 then 1 else recordedActive s p 0)-swapVariation s p 0 ≤
      recordEntropy s p-recordEntropy s (fun j => p j.succ) := by
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun (a : RecordType (fun j => p j.succ)) _ =>
      measurement_mass_imbalance (p 0) (fun b => recordMass s p (Fin.cons b a))
        (fun b => (record_normalization d (n+1) s p).1 _))
  have hm : (∑ a : RecordType (fun j => p j.succ),
      if (p 0).outcomes=2 then ∑ b, recordMass s p (Fin.cons b a)
      else ∑ b, if b=(p 0).index 0 then 0 else recordMass s p (Fin.cons b a)) =
      if (p 0).outcomes=2 then 1 else recordedActive s p 0 := by
    split_ifs with hp
    · simp only [hp, ite_true, record_mass_tail]
      exact (record_normalization d n s (fun j => p j.succ)).2
    · simp only [hp, ite_false, recordedActive, Recording.sum_records_cons, Fin.cons_zero]
      exact Finset.sum_comm
  have hv : (∑ a : RecordType (fun j => p j.succ),
      (∑ b : Fin (p 0).outcomes, |recordMass s p (Fin.cons b a)-
        recordMass s p (Fin.cons ((p 0).swap b) a)|)/2) = swapVariation s p 0 := by
    rw [swapVariation, Recording.sum_records_cons, Finset.sum_comm]
    simp only [swap_record_cons_zero, Finset.sum_div]
  simp only [Finset.sum_sub_distrib, record_mass_tail] at h
  simp only [record_mass_tail] at hm
  rw [hm, hv] at h
  have hc := record_entropy_chain s p
  linarith

 theorem swap_variation_cast {d m n : ℕ} (s : State d) (h : m=n)
    (p : Fin m → Measurement d) (q : Fin n → Measurement d)
    (hp : ∀ j, p j=q (Fin.cast h j)) (i : Fin m) :
    swapVariation s p i=swapVariation s q (Fin.cast h i) := by
  subst n
  have hpq : p=q := funext hp
  subst q
  rfl

 theorem suffix_variation_succ {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d) (i : Fin n) :
    swapVariation s (suffix p i.succ.val) ⟨0, by omega⟩ =
      swapVariation s (suffix (fun j => p j.succ) i.val) ⟨0, by omega⟩ := by
  rcases i with ⟨k,hk⟩
  have hlen : (n+1)-(k+1)=n-k := by omega
  have hp : ∀ j : Fin ((n+1)-(k+1)),
      suffix p (k+1) j=suffix (fun j => p j.succ) k (Fin.cast hlen j) := by
    intro j
    apply congrArg p
    apply Fin.ext
    change k+1+j.val=k+(Fin.cast hlen j).val+1
    simp only [Fin.val_cast]
    omega
  have h := swap_variation_cast s hlen (suffix p (k+1)) (suffix (fun j => p j.succ) k) hp ⟨0, by omega⟩
  have hi : Fin.cast hlen (⟨0, by omega⟩ : Fin ((n+1)-(k+1)))=(⟨0, by omega⟩ : Fin (n-k)) := Fin.ext rfl
  rw [hi] at h
  exact h
 theorem classical_chain_lower : Turn9.ClassicalChainLower := by
  intro d m s p
  induction m with
  | zero =>
    simp [binaryCount, recordEntropy, recordMass, reverseWord, state_hs_xi]
  | succ n ih =>
    let tail : Fin n → Measurement d := fun j => p j.succ
    have hi := ih tail
    have hh := head_entropy_lower s p
    have hbN : binaryCount p=(if (p 0).outcomes=2 then 1 else 0)+binaryCount tail := by
      simp only [binaryCount, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ, tail]
    have hb : (binaryCount p:ℝ)=(if (p 0).outcomes=2 then 1 else 0)+(binaryCount tail:ℝ) := by
      exact_mod_cast hbN
    have ha : (∑ i ∈ Finset.univ.filter (fun i => (p i).outcomes=3), recordedActive s p i) =
        (if (p 0).outcomes=3 then recordedActive s p 0 else 0)+
          ∑ i ∈ Finset.univ.filter (fun i => (tail i).outcomes=3), recordedActive s tail i := by
      simp only [Finset.sum_filter, Fin.sum_univ_succ, recorded_active_succ, tail]
    have hv : (∑ i : Fin (n+1), swapVariation s (suffix p i.val) ⟨0, by omega⟩) =
        swapVariation s p 0+∑ i : Fin n, swapVariation s (suffix tail i.val) ⟨0, by omega⟩ := by
      rw [Fin.sum_univ_succ]
      have hz : suffix p 0=p := by
        funext j
        dsimp [suffix]
        congr 1
        apply Fin.ext
        simp
      have hzidx : (⟨0, by omega⟩ : Fin (n+1))=0 := Fin.ext rfl
      simp only [Fin.val_zero, hz, suffix_variation_succ, tail, hzidx]
    rw [hb, ha, hv]
    rcases (p 0).arity with h2 | h3
    · have h3 : (p 0).outcomes≠3 := by omega
      simp [h2, h3] at hh ⊢
      dsimp [tail] at hi
      linarith
    · have h2 : (p 0).outcomes≠2 := by omega
      simp [h2, h3] at hh ⊢
      dsimp [tail] at hi
      linarith

end
end E2








