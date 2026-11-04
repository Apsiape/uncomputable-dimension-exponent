import E2.CountActivation
import E2.CountEntropyScalar

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 400000

 theorem ternary_mass_imbalance (a b c : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) :
    b+c-|b-c| ≤ (Real.negMulLog a+Real.negMulLog b+Real.negMulLog c-Real.negMulLog (a+b+c))/Real.log 2 := by
  have h := binary_mass_imbalance b c hb hc
  rw [binary_mass_entropy_log b c hb hc] at h
  have hnon : 0≤(a+(b+c))*binaryEntropy (a/(a+(b+c))) :=
    mul_nonneg (by positivity) (div_nonneg (Real.binEntropy_nonneg (by positivity)
      (by by_cases hz : a+(b+c)=0; simp [hz]; apply (div_le_one (by positivity : 0<a+(b+c))).mpr; linarith))
      (Real.log_pos (by norm_num)).le)
  rw [binary_mass_entropy_log a (b+c) ha (add_nonneg hb hc)] at hnon
  simp only [add_div, sub_div] at h hnon ⊢
  have he : Real.negMulLog (a+(b+c))=Real.negMulLog (a+b+c) := by congr 1; ring
  rw [he] at hnon
  linarith

 theorem record_mass_tail {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d)
    (a : RecordType (fun j => p j.succ)) :
    (∑ b : Fin (p 0).outcomes, recordMass s p (Fin.cons b a))=recordMass s (fun j => p j.succ) a := by
  have hP : (∑ b, ((p 0).projection b).conjTranspose*(p 0).projection b)=1 := by
    simpa only [(p 0).selfadjoint, (p 0).idempotent] using (p 0).complete
  simp only [recordMass, reverse_word_cons, Matrix.mul_assoc]
  exact Recording.parseval_left (p 0).projection hP _

/-- Exact reverse-order entropy chain, expressed with unnormalized cell masses. -/
 theorem record_entropy_chain {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d) :
    recordEntropy s p = recordEntropy s (fun j => p j.succ)+
      ∑ a : RecordType (fun j => p j.succ),
        ((∑ b : Fin (p 0).outcomes, Real.negMulLog (recordMass s p (Fin.cons b a)))-
          Real.negMulLog (recordMass s (fun j => p j.succ) a))/Real.log 2 := by
  rw [recordEntropy, Recording.sum_records_cons, Finset.sum_comm]
  simp only [recordEntropy, ←Finset.sum_div, Finset.sum_sub_distrib]
  ring

 theorem swap_record_cons_zero {d n : ℕ} (p : Fin (n+1) → Measurement d)
    (b : Fin (p 0).outcomes) (a : RecordType (fun j => p j.succ)) :
    swapRecord p 0 (Fin.cons b a)=Fin.cons ((p 0).swap b) a := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [swapRecord]
  · simp [swapRecord, Function.update_of_ne (Fin.succ_ne_zero k)]

 theorem recorded_active_succ {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d) (i : Fin n) :
    recordedActive s p i.succ=recordedActive s (fun j => p j.succ) i := by
  rw [recorded_active_complement, recorded_active_complement, marginal_mass_succ]

 theorem measurement_mass_imbalance {d : ℕ} (P : Measurement d) (w : Fin P.outcomes → ℝ)
    (hw : ∀ b, 0≤w b) :
    (if P.outcomes=2 then ∑ b, w b else ∑ b, if b=P.index 0 then 0 else w b)-
      (∑ b, |w b-w (P.swap b)|)/2 ≤
        ((∑ b, Real.negMulLog (w b))-Real.negMulLog (∑ b, w b))/Real.log 2 := by
  rcases P with ⟨o, harity, proj, hsa, hid, hort, hcomp⟩
  rcases harity with h | h
  · subst o
    have h := binary_mass_imbalance (w 0) (w 1) (hw 0) (hw 1)
    rw [binary_mass_entropy_log _ _ (hw 0) (hw 1)] at h
    simpa [Measurement.swap, Measurement.index, Fin.sum_univ_two, Equiv.swap_apply_def, abs_sub_comm,
      add_div, div_self, sub_self] using h
  · subst o
    have h := ternary_mass_imbalance (w 0) (w 1) (w 2) (hw 0) (hw 1) (hw 2)
    simpa [Measurement.swap, Measurement.index, Fin.sum_univ_three, Equiv.swap_apply_def, abs_sub_comm,
      add_div, div_self, sub_self] using h

end
end E2
