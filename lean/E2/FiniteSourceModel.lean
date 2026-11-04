import E2.FiniteSourceRelations

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem quarter_pow_eq (N : ℕ) : (1/4:ℝ)^N=(4:ℝ)^(-(N:ℤ)) := by
  rw [zpow_neg,zpow_natCast,one_div,inv_pow]

def sourceModel (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    Model (sourcePresentation p) (2^(3*N+finiteSlots p N)) (3*(4:ℝ)^(-(N:ℤ))) where
  positive_dimension := by positivity
  state := flatState _ (by positivity)
  value := sourceTuple p N
  domains := sourceTuple_domains p N
  defects r hr := (weighted_le_norm _ _).trans (by
    rw [←quarter_pow_eq]
    exact sourceTuple_all_relations p N hN hEven r hr)
  state_commutators i := by
    rw [flatState_commutes]
    have hz : hs (0:Mat (2^(3*N+finiteSlots p N)))=0 := by
      simp [hs,Companion.Analytic.hsNorm,Companion.Analytic.hsSquared]
    rw [hz]
    positivity

theorem sourceModel_flat (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    (sourceModel p N hN hEven).Flat := by
  change (((2^(3*N+finiteSlots p N):ℕ):ℂ)⁻¹) • 1 =
    (1/((2^(3*N+finiteSlots p N):ℕ):ℂ)) • 1
  rw [one_div]

theorem sourceModel_op_defects (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    ∀ r∈(sourcePresentation p).relations,
      ‖Poly.eval (sourceModel p N hN hEven).value r‖ ≤ 3*(4:ℝ)^(-(N:ℤ)) := by
  change ∀ r∈(sourcePresentation p).relations, ‖Poly.eval (sourceTuple p N) r‖ ≤ 3*(4:ℝ)^(-(N:ℤ))
  rw [←quarter_pow_eq]
  exact sourceTuple_all_relations p N hN hEven

end
end E2.FiniteConstruction
