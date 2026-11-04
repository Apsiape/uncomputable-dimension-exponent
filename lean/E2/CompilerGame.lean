import E2.CompilerBoolean

namespace E2.CompilerGame
noncomputable section
open scoped BigOperators

def incidenceCount {n m : ℕ} (scope : Fin m → Finset (Fin n)) : ℕ :=
  ∑ c, (scope c).card

/-- The ordinary context-variable game with uniform rational incidence weights.
The constructor retains all total Boolean assignments and the original locality
condition; it imposes no parity restriction. -/
def uniform {n m : ℕ} (scope : Fin m → Finset (Fin n))
    (allowed : Fin m → Finset (Fin n → Bool))
    (hnonempty : ∀ c, (allowed c).Nonempty)
    (hlocal : ∀ c a b, (∀ v ∈ scope c, a v=b v) →
      (a ∈ allowed c ↔ b ∈ allowed c))
    (hcount : 0 < incidenceCount scope) : BCSGame where
  numVars := n
  contexts := m
  scope := scope
  allowed := allowed
  valid_nonempty := hnonempty
  locality := hlocal
  probability c v := if v ∈ scope c then (incidenceCount scope : ℚ)⁻¹ else 0
  probability_nonneg c v := by
    split_ifs <;> positivity
  probability_support c v := by
    have hn : (incidenceCount scope : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
    by_cases h : v ∈ scope c <;> simp [h,hn]
  probability_sum := by
    have hn : (incidenceCount scope : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
    have hs (c : Fin m) :
        (∑ v : Fin n, if v ∈ scope c then (incidenceCount scope : ℚ)⁻¹ else 0) =
          ((scope c).card : ℚ) * (incidenceCount scope : ℚ)⁻¹ := by
      simp [Finset.sum_ite, nsmul_eq_mul]
    simp_rw [hs]
    rw [← Finset.sum_mul]
    have hc : (∑ c, ((scope c).card : ℚ)) = (incidenceCount scope : ℚ) := by
      simp [incidenceCount]
    rw [hc,mul_inv_cancel₀ hn]

end
end E2.CompilerGame
