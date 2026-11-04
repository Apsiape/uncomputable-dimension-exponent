import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.ENat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Concrete finite ordinary BCS games, unrestricted POVMs, and mixed states.
Assignments use a total Boolean labeling; `locality` makes labels outside the
context irrelevant. Invalid Alice answers are retained and lose automatically.
-/
namespace E2
noncomputable section
open scoped BigOperators ComplexOrder

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

structure BCSGame where
  numVars : ℕ
  contexts : ℕ
  scope : Fin contexts → Finset (Fin numVars)
  allowed : Fin contexts → Finset (Fin numVars → Bool)
  valid_nonempty : ∀ c, (allowed c).Nonempty
  locality : ∀ c a b, (∀ v ∈ scope c, a v = b v) →
    (a ∈ allowed c ↔ b ∈ allowed c)
  probability : Fin contexts → Fin numVars → ℚ
  probability_nonneg : ∀ c v, 0 ≤ probability c v
  probability_support : ∀ c v, probability c v ≠ 0 ↔ v ∈ scope c
  probability_sum : ∑ c, ∑ v, probability c v = 1

structure Strategy (G : BCSGame) (d : ℕ) where
  rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
  rho_positive : rho.PosSemidef
  rho_trace : Matrix.trace rho = 1
  alice : Fin G.contexts → (Fin G.numVars → Bool) → Mat d
  alice_positive : ∀ c a, (alice c a).PosSemidef
  alice_complete : ∀ c, ∑ a, alice c a = 1
  bob : Fin G.numVars → Bool → Mat d
  bob_positive : ∀ v b, (bob v b).PosSemidef
  bob_complete : ∀ v, ∑ b, bob v b = 1

def winningProbability {G : BCSGame} {d : ℕ} (s : Strategy G d) : ℝ :=
  ∑ c, ∑ v, (G.probability c v : ℝ) *
    ∑ a ∈ G.allowed c,
      (Matrix.trace (s.rho * Matrix.kronecker (s.alice c a) (s.bob v (a v)))).re

def loss {G : BCSGame} {d : ℕ} (s : Strategy G d) : ℝ :=
  1 - winningProbability s

def quantumValue (G : BCSGame) : ℝ :=
  sSup {w | ∃ d : ℕ, 0 < d ∧ ∃ s : Strategy G d, winningProbability s = w}

def Feasible (G : BCSGame) (ε : ℝ) (d : ℕ) : Prop :=
  0 < d ∧ ∃ s : Strategy G d, loss s ≤ ε

/-- Least common local dimension, or infinity when no strategy meets the loss.
Padding smaller local spaces is allowed by the statement's common-space model. -/
def dimension (G : BCSGame) (ε : ℝ) : ℕ∞ := by
  classical
  exact
  if h : ∃ d, Feasible G ε d then (Nat.find h : ℕ∞) else ⊤

def logDimension (G : BCSGame) (ε : ℝ) : ℝ :=
  Real.logb 2 ((dimension G ε).toNat : ℝ)

def NoPerfectStrategy (G : BCSGame) : Prop :=
  ∀ d, 0 < d → ∀ s : Strategy G d, loss s ≠ 0

def DimensionExponent (G : BCSGame) (β : ℝ) : Prop :=
  (∀ ε, 0 < ε → dimension G ε ≠ ⊤) ∧
  Filter.Tendsto (fun ε : ℝ => logDimension G ε / Real.logb 2 (1 / ε))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds β)

def dyadicSlope (G : BCSGame) (n : ℕ) : ℝ :=
  logDimension G ((2 : ℝ) ^ (-(n : ℤ))) / n

end
end E2
