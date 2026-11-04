import E2.Joint
import E2.FiniteCutoff
import E2.FiniteSourceModel

namespace E2
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

def haltsWithin (p : CounterProgram) (e T : ℕ) : Bool :=
  (List.range T).any (fun t => decide (((p.step)^[t] (p.initial e)).control=p.halt))
def thetaN (p : CounterProgram) (N : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (N/2), if haltsWithin p e (2^N) then haltingWeight e else 0

/-- Theorem 7.1, including the operator-norm bound for every source relation.
The integer exponent is explicit, rather than an unquantified O-term. -/
theorem simultaneous_finite_models (p : CounterProgram) (hp : RecognizesK p) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → Even N →
      ∃ k : ℕ, |(k:ℝ)-thetaN p N*N| ≤ C*Real.logb 2 (N+2) ∧
        ∃ m : Model (sourcePresentation p) (2^(3*N+k)) (3*(4:ℝ)^(-(N:ℤ))),
          m.Flat ∧ ∀ r ∈ (sourcePresentation p).relations,
            ‖Poly.eval m.value r‖ ≤ 3*(4:ℝ)^(-(N:ℤ)) := by
  classical
  refine ⟨4,by norm_num,?_⟩
  intro N hN hEven
  have hdet (e : ℕ) : haltsWithin p e (2^N)=true ↔ FiniteConstruction.detected p e N := by
    simp [haltsWithin,FiniteConstruction.detected,List.any_eq_true]
  have he : thetaN p N=∑' e, FiniteConstruction.cutoff p N e := by
    rw [FiniteConstruction.cutoff_eq_sum]
    unfold thetaN
    apply Finset.sum_congr rfl
    intro e he
    by_cases hd : FiniteConstruction.detected p e N
    · have ht := (hdet e).mpr hd
      simp [ht,hd]
    · have ht : haltsWithin p e (2^N)=false := Bool.eq_false_iff.mpr (fun h => hd ((hdet e).mp h))
      simp [ht,hd]
  refine ⟨FiniteConstruction.finiteSlots p N,?_,FiniteConstruction.sourceModel p N hN hEven,
    FiniteConstruction.sourceModel_flat p N hN hEven,
    FiniteConstruction.sourceModel_op_defects p N hN hEven⟩
  rw [he]
  exact FiniteConstruction.sourceTuple_exponent_bound p N hN

theorem finite_flag_limit (p : CounterProgram) (hp : RecognizesK p) :
    Monotone (thetaN p) ∧ Filter.Tendsto (thetaN p) Filter.atTop (nhds thetaK) := by
  classical
  have hdet (e N : ℕ) : haltsWithin p e (2^N) = true ↔ FiniteConstruction.detected p e N := by
    simp [haltsWithin,FiniteConstruction.detected,List.any_eq_true]
  have hsum (N : ℕ) : thetaN p N = ∑' e, FiniteConstruction.cutoff p N e := by
    rw [FiniteConstruction.cutoff_eq_sum]
    unfold thetaN
    apply Finset.sum_congr rfl
    intro e he
    simp only [hdet]
  rw [show thetaN p = (fun N => ∑' e, FiniteConstruction.cutoff p N e) from funext hsum]
  exact ⟨FiniteConstruction.cutoff_sum_monotone p,FiniteConstruction.cutoff_limit p hp⟩

end
end E2
