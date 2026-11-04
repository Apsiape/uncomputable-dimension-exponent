import Companion.HilbertSchmidt
import E2.Game
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

abbrev State := Companion.Analytic.State
abbrev hs := @Companion.Analytic.hsNorm
abbrev comm := @Companion.Analytic.comm

def weighted {d : ℕ} (s : State d) (D : Mat d) : ℝ := hs (D * s.xi)
def expectation {d : ℕ} (s : State d) (D : Mat d) : ℝ :=
  (Matrix.trace (s.rho * D)).re

inductive Domain
  | positiveContraction | projection | reflection | unitary
  deriving DecidableEq, Repr

def Domain.Holds {d : ℕ} : Domain → Mat d → Prop
  | .positiveContraction, a => a.PosSemidef ∧ (1 - a).PosSemidef
  | .projection, a => a.conjTranspose = a ∧ a * a = a
  | .reflection, a => a.conjTranspose = a ∧ a * a = 1
  | .unitary, a => a.conjTranspose * a = 1 ∧ a * a.conjTranspose = 1

/-- Finite rational real-coefficient noncommutative *-polynomials. -/
inductive Poly (ι : Type*)
  | const : ℚ → Poly ι
  | var : ι → Poly ι
  | add : Poly ι → Poly ι → Poly ι
  | mul : Poly ι → Poly ι → Poly ι
  | adj : Poly ι → Poly ι
  deriving Repr

namespace Poly
variable {ι : Type*}
instance : Add (Poly ι) := ⟨.add⟩
instance : Mul (Poly ι) := ⟨.mul⟩
instance : Neg (Poly ι) := ⟨fun p => .mul (.const (-1)) p⟩
instance : Sub (Poly ι) := ⟨fun p q => .add p (-q)⟩
instance (n : ℕ) : OfNat (Poly ι) n := ⟨.const n⟩
instance : Pow (Poly ι) ℕ := ⟨fun p n => (List.replicate n p).foldr .mul 1⟩
def eval {d : ℕ} (x : ι → Mat d) : Poly ι → Mat d
  | .const q => (q : ℂ) • 1
  | .var i => x i
  | .add p q => eval x p + eval x q
  | .mul p q => eval x p * eval x q
  | .adj p => (eval x p).conjTranspose
end Poly

structure Presentation (ι : Type*) where
  domain : ι → Domain
  relations : List (Poly ι)

structure Model {ι : Type*} (P : Presentation ι) (d : ℕ) (δ : ℝ) where
  positive_dimension : 0 < d
  state : State d
  value : ι → Mat d
  domains : ∀ i, (P.domain i).Holds (value i)
  defects : ∀ r ∈ P.relations, weighted state (Poly.eval value r) ≤ δ
  state_commutators : ∀ i, hs (comm (value i) state.xi) ≤ δ

def Model.weaken {ι : Type*} {P : Presentation ι} {d : ℕ} {δ η : ℝ}
    (m : Model P d δ) (h : δ ≤ η) : Model P d η where
  positive_dimension := m.positive_dimension
  state := m.state
  value := m.value
  domains := m.domains
  defects := fun r hr => (m.defects r hr).trans h
  state_commutators := fun i => (m.state_commutators i).trans h

def Model.Flat {ι : Type*} {P : Presentation ι} {d : ℕ} {δ : ℝ}
    (m : Model P d δ) : Prop := m.state.rho = (1 / (d : ℂ)) • 1

def modelDimension {ι : Type*} (P : Presentation ι) (flat : Bool) (δ : ℝ) : ℕ∞ := by
  classical
  exact
  if h : ∃ d, ∃ m : Model P d δ, flat = true → m.Flat
    then (Nat.find h : ℕ∞) else ⊤

def W {ι : Type*} (P : Presentation ι) := modelDimension P false
def H {ι : Type*} (P : Presentation ι) := modelDimension P true

end
end E2
