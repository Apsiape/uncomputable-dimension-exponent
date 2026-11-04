import E2.SeparatedDigits
import Mathlib.Analysis.Normed.Group.Tannery

namespace E2.HaltingApproximation
noncomputable section
set_option maxHeartbeats 300000
open Encodable EffectiveCoding SeparatedDigits Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Nat.Partrec.Code

def stageTerm (s e : ℕ) : ℚ :=
  if (evaln s (ofNatCode e) 0).isSome then (1:ℚ)/(4:ℚ)^(e+1) else 0

def stage (s : ℕ) : ℚ := ∑ e ∈ Finset.range s, stageTerm s e

theorem stageTerm_computable : Computable₂ stageTerm := by
  have hc : Computable (fun p : ℕ × ℕ => ofNatCode p.2) := by
    simpa only [← ofNatCode_eq] using (Computable.ofNat Nat.Partrec.Code).comp Computable.snd
  have he : Computable (fun p : ℕ × ℕ => evaln p.1 (ofNatCode p.2) 0) :=
    primrec_evaln.to_comp.comp ((Computable.fst.pair hc).pair (Computable.const 0))
  have hp : Primrec (fun e : ℕ => 4^(e+1)) :=
    Primrec₂.unpaired'.mp Nat.Primrec.pow |>.comp (Primrec.const 4) Primrec.succ
  refine ((Primrec.option_isSome.to_comp.comp he).cond
    (rat_divNat.comp ((Computable.const 1).pair (hp.to_comp.comp Computable.snd)))
    (Computable.const 0)).of_eq ?_
  intro p
  simp only [stageTerm]
  split <;> simp_all

theorem sum_computable (f : ℕ × ℕ → ℚ) (hf : Computable f) :
    Computable (fun s => ∑ e ∈ Finset.range s, f (s,e)) := by
  let step : ℕ → ℕ → ℕ → ℕ := fun s e acc => encode (rationalCode acc + f (s,e))
  have hstep : Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) => step p.1.1 p.2.1 p.2.2) :=
    Computable.encode.comp (rat_add.comp
      (rational_decode.to_comp.comp (Computable.snd.comp Computable.snd))
      (hf.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd))))
  have hrec : Computable (fun p : ℕ × ℕ =>
      Nat.rec (motive := fun _ => ℕ) (encode (0:ℚ)) (step p.1) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const (encode (0:ℚ))) hstep.to₂
  have he (s n : ℕ) : rationalCode (Nat.rec (encode (0:ℚ)) (step s) n) =
      ∑ e ∈ Finset.range n, f (s,e) := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Nat.rec_add_one,step,rational_encode,Finset.sum_range_succ,ih]
  exact ((rational_decode.to_comp).comp (hrec.comp
    (Computable.id.pair Computable.id))).of_eq (fun s => he s s)

theorem stage_computable : Computable stage := by
  exact sum_computable (fun p => stageTerm p.1 p.2) stageTerm_computable

def realTerm (s e : ℕ) : ℝ := if e < s then (stageTerm s e : ℝ) else 0

theorem realTerm_bounds (s e : ℕ) : 0 ≤ realTerm s e ∧ realTerm s e ≤ haltingWeight e := by
  have he : (↑((1:ℚ)/(4:ℚ)^(e+1)) : ℝ) = haltingWeight e := by
    push_cast
    unfold haltingWeight
    rw [show -(e+1:ℤ) = -((e+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
    simp only [one_div]
  unfold realTerm stageTerm
  split_ifs <;> simp_all [le_of_lt (weight_positive e)]

theorem realTerm_pointwise (e : ℕ) : Tendsto (fun s => realTerm s e) atTop
    (nhds ((bit haltingSet e : ℝ)*haltingWeight e)) := by
  by_cases h : e ∈ haltingSet
  · obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t,ht⟩ := evaln_complete.mp hv
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max (e+1) t)] with s hs
    have hst : t ≤ s := (le_max_right _ _).trans hs
    have hse : e < s := by have := (le_max_left (e+1) t).trans hs; omega
    have hi : (evaln s (ofNatCode e) 0).isSome = true :=
      Option.isSome_iff_exists.mpr ⟨v,evaln_mono hst ht⟩
    simp only [realTerm,hse,↓reduceIte,stageTerm,hi,bit,h,Nat.cast_one,one_mul]
    push_cast
    unfold haltingWeight
    rw [show -(e+1:ℤ) = -((e+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
    simp only [one_div]
  · have hi : ∀ s, (evaln s (ofNatCode e) 0).isSome = false := by
      intro s
      by_contra hbad
      obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (by cases hq : (evaln s (ofNatCode e) 0).isSome <;> simp_all)
      exact h (Part.dom_iff_mem.mpr ⟨v,evaln_sound hv⟩)
    convert (tendsto_const_nhds (x := (0:ℝ))) using 1
    · funext s
      simp [realTerm,stageTerm,hi]
    · simp [bit,h]

theorem stage_limit : Tendsto (fun s => (stage s : ℝ)) atTop (nhds thetaK) := by
  have h := tendsto_tsum_of_dominated_convergence weight_summable realTerm_pointwise
    (by
      apply Filter.Eventually.of_forall
      intro s e
      rw [Real.norm_eq_abs,abs_of_nonneg (realTerm_bounds s e).1]
      exact (realTerm_bounds s e).2)
  have he : ∀ s, (∑' e, realTerm s e) = (stage s : ℝ) := by
    intro s
    rw [tsum_eq_sum (s := Finset.range s)]
    · simp only [stage,Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro e he
      simp only [realTerm,Finset.mem_range.mp he,↓reduceIte]
    · intro e he
      simp only [realTerm,ite_eq_right_iff]
      intro hh
      exact (he (Finset.mem_range.mpr hh)).elim
  simp_rw [he] at h
  change Tendsto (fun s => (stage s : ℝ)) atTop (nhds (value haltingSet)) at h
  simpa only [← theta_value] using h

theorem stage_le (s : ℕ) : (stage s : ℝ) ≤ thetaK := by
  rw [theta_value,value]
  have hsum : Summable (realTerm s) := Summable.of_nonneg_of_le
    (fun e => (realTerm_bounds s e).1) (fun e => (realTerm_bounds s e).2) weight_summable
  have he : (stage s : ℝ) = ∑' e, realTerm s e := by
    rw [tsum_eq_sum (s := Finset.range s)]
    · simp only [stage,Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro e he
      simp only [realTerm,Finset.mem_range.mp he,ite_true]
    · intro e he
      simp only [realTerm,Finset.mem_range] at *
      simp [he]
  rw [he]
  apply hsum.tsum_le_tsum _ (series_summable haltingSet)
  intro e
  by_cases h : e ∈ haltingSet
  · simpa [bit,h] using (realTerm_bounds s e).2
  · have hi : (evaln s (ofNatCode e) 0).isSome = false := by
      cases hh : evaln s (ofNatCode e) 0 with
      | none => rfl
      | some v => exact (h (Part.dom_iff_mem.mpr ⟨v,evaln_sound hh⟩)).elim
    simp [realTerm,stageTerm,hi,bit,h]

end
end E2.HaltingApproximation
