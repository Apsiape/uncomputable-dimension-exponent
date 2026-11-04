import E2.Measurements

namespace E2
noncomputable section

/-- Theorem 4.4, with its O(log(n+2)) terms quantified uniformly. -/
theorem clock_profile : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    W clockPresentation ((2:ℝ)^(-(n:ℤ))) ≠ ⊤ ∧
    H clockPresentation ((2:ℝ)^(-(n:ℤ))) ≠ ⊤ ∧
    |Real.logb 2 ((W clockPresentation ((2:ℝ)^(-(n:ℤ)))).toNat : ℝ) - n/2| ≤ C*Real.logb 2 (n+2) ∧
    |Real.logb 2 ((H clockPresentation ((2:ℝ)^(-(n:ℤ)))).toNat : ℝ) - n/2| ≤ C*Real.logb 2 (n+2) := by
  sorry

end
end E2
