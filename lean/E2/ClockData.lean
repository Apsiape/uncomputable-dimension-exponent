import E2.Source
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def cantorCoordinate (bits : ℕ → Bool) : ℝ :=
  ∑' j : ℕ, if bits j then 3 * (4 : ℝ) ^ (-(j + 1 : ℤ)) else 0
def cantorSet : Set ℝ := Set.range cantorCoordinate
def digitFunction (x : ℝ) : ℝ :=
  if x ≤ 1/4 then 0 else if x ≤ 3/4 then 2*x - 1/2 else 1
def tailFunction (x : ℝ) : ℝ := 4*x - 3*digitFunction x
def digitAt (j : ℕ) (x : ℝ) : ℝ := digitFunction (tailFunction^[j] x)

def matrixFunction {d : ℕ} (g : ℝ → ℝ) (a : Mat d) : Mat d := cfc g a
def HasCantorSpectrum {d : ℕ} (a : Mat d) : Prop :=
  a.IsHermitian ∧ spectrum ℝ a ⊆ cantorSet
def translate {d : ℕ} (u a : Mat d) (i : ℕ) : Mat d :=
  u ^ i * a * u.conjTranspose ^ i

structure ClockData (d : ℕ) where
  A : Mat d
  P : Mat d
  T : Mat d
  X : Mat d

def ClockData.variables {d : ℕ} (c : ClockData d) : List (Mat d) := [c.A,c.P,c.T,c.X]
def ClockData.defects {d : ℕ} (c : ClockData d) : List (Mat d) :=
  [comm c.A c.P, c.T*c.A*c.T.conjTranspose - ((4:ℂ) • c.A - (3:ℂ) • c.P),
   c.X*c.P*c.X - (1-c.P), comm c.X (c.T*c.A*c.T.conjTranspose)]
def ClockData.Valid {d : ℕ} (c : ClockData d) : Prop :=
  Domain.positiveContraction.Holds c.A ∧ Domain.projection.Holds c.P ∧
  Domain.unitary.Holds c.T ∧ Domain.reflection.Holds c.X
def ClockApprox {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d) : Prop :=
  c.Valid ∧ (∀ r ∈ c.defects, weighted s r ≤ δ) ∧
    (∀ v ∈ c.variables, hs (comm v s.xi) ≤ δ)
def rawDigit {d : ℕ} (c : ClockData d) (j : ℕ) := translate c.T c.P j
def rawFlip {d : ℕ} (c : ClockData d) (j : ℕ) := translate c.T c.X j

structure SpectralRepair {d : ℕ} (c : ClockData d) (s : State d) (δ C : ℝ) where
  Ahat : Mat d
  spectrum : HasCantorSpectrum Ahat
  closeness : weighted s (Ahat - c.A) + hs (comm Ahat s.xi) ≤ C*δ
  digits : ∀ j, weighted s (rawDigit c j - matrixFunction (digitAt j) Ahat) ≤ C*4^j*δ

end
end E2
