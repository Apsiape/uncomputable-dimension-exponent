import E2.ClockData

namespace E2
noncomputable section
open scoped BigOperators

def addBits (i : ℕ) (b : ℕ → Bool) (j : ℕ) : Bool :=
  decide (((i + ∑ k ∈ Finset.range (j+1), if b k then 2^k else 0) / 2^j) % 2 = 1)

def carryOnBits (b : ℕ → Bool) : ℝ := by
  classical
  exact if h : ∃ k, b k = false then (4:ℝ)^(-(Nat.find h : ℤ)) else 0

/-- The concrete McShane extensions used by the blueprint. -/
def cantorTranslation (i : ℕ) (x : ℝ) : ℝ :=
  sInf (Set.range (fun b : ℕ → Bool => cantorCoordinate (addBits i b) + 2*|x-cantorCoordinate b|))
def carryFunction (x : ℝ) : ℝ :=
  sInf (Set.range (fun b : ℕ → Bool => carryOnBits b + 2*|x-cantorCoordinate b|))

end
end E2
