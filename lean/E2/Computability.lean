import E2.Game
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringDegree
import Mathlib.Data.Rat.Encodable

namespace E2
noncomputable section
open scoped BigOperators

/-- The standard effective enumeration is Mathlib's partial-recursive codes,
run on input zero. Changing acceptable numberings preserves the Turing degree. -/
def haltingSet : Set ℕ :=
  {e | (Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) 0).Dom}

def haltingWeight (e : ℕ) : ℝ := (4 : ℝ) ^ (-(e + 1 : ℤ))
def thetaK : ℝ := by
  classical
  exact ∑' e : ℕ, if e ∈ haltingSet then haltingWeight e else 0
def betaK : ℝ := (3 + thetaK) / 4

/-- Mathlib's rational decoding enumerates every rational; unused codes give 0. -/
def rationalCode (n : ℕ) : ℚ :=
  (Encodable.decode (α := ℚ) n).getD 0

def realOracle (x : ℝ) : ℕ →. ℕ := by
  classical
  exact fun n => Part.some (if (rationalCode n : ℝ) < x then 1 else 0)

def haltingOracle : ℕ →. ℕ := by
  classical
  exact fun e => Part.some (if e ∈ haltingSet then 1 else 0)

def ExponentHasHaltingDegree : Prop :=
  TuringEquivalent (realOracle betaK) haltingOracle

def ComputableReal (x : ℝ) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ ∀ k,
    |(rationalCode (f k) : ℝ)-x| ≤ (2:ℝ)^(-(k+1:ℤ))

/-- A uniform algorithm for arbitrary rational approximations of each entry. -/
def ComputableRealSequence (a : ℕ → ℝ) : Prop :=
  ∃ f : ℕ × ℕ → ℕ, Computable f ∧ ∀ n k,
    |(rationalCode (f (n,k)) : ℝ)-a n| ≤ (2:ℝ)^(-(k+1:ℤ))

/-- A computable real-valued error envelope, allowed to hold only eventually.
No effective threshold is supplied; a fixed threshold can be hardcoded. -/
def CertifiedRate (a : ℕ → ℝ) (β : ℝ) : Prop :=
  ∃ r : ℕ → ℝ, ComputableRealSequence r ∧
    Filter.Tendsto r Filter.atTop (nhds 0) ∧
    ∀ᶠ n in Filter.atTop, |a n - β| ≤ r n

end
end E2
