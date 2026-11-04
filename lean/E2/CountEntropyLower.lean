import E2.CountClassical

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

 theorem record_entropy_lower : Turn9.RecordEntropyLower := by
  obtain ⟨Cs,hCs,hswap⟩ := suffix_swap_bound
  obtain ⟨Ca,hCa,hactive⟩ := active_probability_transport
  refine ⟨Cs+Ca, by positivity, ?_⟩
  intro d m s η p u hη hrel
  have hchain := classical_chain_lower d m s p
  have hvar : (∑ i : Fin m, swapVariation s (suffix p i.val) ⟨0, by omega⟩)≤Cs*m^3*η := by
    calc
      _ ≤ ∑ _i : Fin m, Cs*(m:ℝ)^2*η := Finset.sum_le_sum (fun i _ => hswap d m s η p u hη hrel i)
      _ = _ := by simp; ring
  let ternary := Finset.univ.filter (fun i : Fin m => (p i).outcomes=3)
  have htransport : activeSum s p≤(∑ i∈ternary, recordedActive s p i)+Ca*m^2*η := by
    have hsum := Finset.sum_le_sum (s:=ternary) (fun i hi =>
      show expectation s (p i).active≤recordedActive s p i+Ca*m*η from by
        have h := hactive d m s η p hη hrel.2.1 i (Finset.mem_filter.mp hi).2
        linarith [(abs_le.mp h).1])
    have hcard : (ternary.card:ℝ)≤m := by
      have hc : ternary.card≤m := by
        calc
          _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = m := by simp
      exact_mod_cast hc
    have hbound : (∑ _i∈ternary, Ca*(m:ℝ)*η)≤Ca*m^2*η := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      calc
        _ ≤ (m:ℝ)*(Ca*m*η) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring
    rw [Finset.sum_add_distrib] at hsum
    exact hsum.trans (add_le_add (le_refl _) hbound)
  by_cases hm : m=0
  · subst m
    simpa [binaryCount, activeSum] using hchain
  · have hm1 : (1:ℝ)≤m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    have hp : Ca*m^2*η≤Ca*m^3*η := by
      have hpow : (m:ℝ)^2≤(m:ℝ)^3 := by nlinarith [sq_nonneg (m:ℝ)]
      nlinarith [mul_le_mul_of_nonneg_right hpow (show 0≤Ca*η by positivity)]
    change (binaryCount p:ℝ)+(∑ i∈ternary, recordedActive s p i)-_≤_ at hchain
    nlinarith

end
end E2

