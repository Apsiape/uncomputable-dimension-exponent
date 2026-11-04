import E2.Joint
import Mathlib.Analysis.Normed.Group.Tannery

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

def detected (p : CounterProgram) (e N : ℕ) : Prop :=
  ∃ t < 2^N, ((p.step)^[t] (p.initial e)).control = p.halt

def cutoff (p : CounterProgram) (N e : ℕ) : ℝ :=
  if e < N/2 ∧ detected p e N then haltingWeight e else 0

theorem weight_nonneg (e : ℕ) : 0 ≤ haltingWeight e := by
  unfold haltingWeight
  positivity

theorem weight_summable : Summable haltingWeight := by
  have h := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1:ℝ)/4 < 1)).mul_left (1/4)
  convert h using 1
  ext e
  simp only [haltingWeight,show (-(e+1:ℤ)) = -((e+1:ℕ):ℤ) by omega,
    zpow_neg,zpow_natCast,pow_succ,one_div,inv_pow]
  ring

theorem detected_mono (p : CounterProgram) (e : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    detected p e M → detected p e N := by
  rintro ⟨t,ht,hh⟩
  exact ⟨t,ht.trans_le (Nat.pow_le_pow_right (by omega) hMN),hh⟩

theorem cutoff_nonneg (p : CounterProgram) (N e : ℕ) : 0 ≤ cutoff p N e := by
  unfold cutoff
  split_ifs
  · exact weight_nonneg e
  · exact le_rfl

theorem cutoff_le (p : CounterProgram) (N e : ℕ) : cutoff p N e ≤ haltingWeight e := by
  unfold cutoff
  split_ifs
  · exact le_rfl
  · exact weight_nonneg e

theorem cutoff_summable (p : CounterProgram) (N : ℕ) : Summable (cutoff p N) := by
  exact Summable.of_nonneg_of_le (cutoff_nonneg p N) (cutoff_le p N) weight_summable

theorem cutoff_monotone (p : CounterProgram) (e : ℕ) : Monotone (fun N => cutoff p N e) := by
  intro M N hMN
  change cutoff p M e ≤ cutoff p N e
  unfold cutoff
  split_ifs with hM hN hN
  · exact le_rfl
  · exact False.elim (hN ⟨hM.1.trans_le (Nat.div_le_div_right hMN),detected_mono p e hMN hM.2⟩)
  · exact weight_nonneg e
  · exact le_rfl

theorem cutoff_eq_sum (p : CounterProgram) (N : ℕ) :
    (∑' e, cutoff p N e) = ∑ e ∈ Finset.range (N/2),
      if detected p e N then haltingWeight e else 0 := by
  classical
  rw [tsum_eq_sum (s := Finset.range (N/2))]
  · apply Finset.sum_congr rfl
    intro e he
    simp only [cutoff,Finset.mem_range.mp he,true_and]
  · intro e he
    simp only [Finset.mem_range,not_lt] at he
    simp [cutoff,show ¬e<N/2 by omega]

theorem cutoff_pointwise (p : CounterProgram) (hp : RecognizesK p) (e : ℕ) :
    Tendsto (fun N => cutoff p N e) atTop
      (nhds (if e ∈ haltingSet then haltingWeight e else 0)) := by
  classical
  by_cases he : e ∈ haltingSet
  · obtain ⟨t,ht⟩ := (hp e).mpr he
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max (2*(e+1)) (t+1))] with N hN
    have hcut : e < N/2 := by omega
    have htN : t < 2^N := by
      exact (show t<N by omega).trans (Nat.lt_two_pow_self (n := N))
    simp [cutoff,hcut,detected,he,show ∃ t<2^N,
      ((p.step)^[t] (p.initial e)).control=p.halt from ⟨t,htN,ht⟩]
  · have hdet (N : ℕ) : ¬ detected p e N := by
      rintro ⟨t,_,ht⟩
      exact he ((hp e).mp ⟨t,ht⟩)
    simpa [cutoff,hdet,he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))

theorem cutoff_limit (p : CounterProgram) (hp : RecognizesK p) :
    Tendsto (fun N => ∑' e, cutoff p N e) atTop (nhds thetaK) := by
  unfold thetaK
  apply tendsto_tsum_of_dominated_convergence weight_summable (cutoff_pointwise p hp)
  exact Filter.Eventually.of_forall (fun N e => by
    rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg p N e)]
    exact cutoff_le p N e)

theorem cutoff_sum_monotone (p : CounterProgram) : Monotone (fun N => ∑' e, cutoff p N e) := by
  intro M N hMN
  exact (cutoff_summable p M).tsum_le_tsum (fun e => cutoff_monotone p e hMN) (cutoff_summable p N)

end
end E2.FiniteConstruction
