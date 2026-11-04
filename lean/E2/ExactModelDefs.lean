import E2.Clock
import E2.ExactZeroTest

namespace E2
noncomputable section
open scoped BigOperators

variable {A : Type*} [CStarAlgebra A]

structure TracialState (A : Type*) [CStarAlgebra A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  normalized : toLinearMap 1 = 1
  positive : ∀ a, 0 ≤ (toLinearMap (star a * a)).re
  cyclic : ∀ a b, toLinearMap (a*b) = toLinearMap (b*a)

def Domain.HoldsC : Domain → A → Prop
  | .positiveContraction, a => IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1
  | .projection, a => star a = a ∧ a*a = a
  | .reflection, a => star a = a ∧ a*a = 1
  | .unitary, a => star a*a = 1 ∧ a*star a = 1

def Poly.evalC {ι : Type*} (x : ι → A) : Poly ι → A
  | .const q => (q : ℂ) • 1
  | .var i => x i
  | .add p q => p.evalC x + q.evalC x
  | .mul p q => p.evalC x * q.evalC x
  | .adj p => star (p.evalC x)

structure ExactModel {ι : Type*} (P : Presentation ι) (A : Type*) [CStarAlgebra A] where
  state : TracialState A
  value : ι → A
  domains : ∀ i, (P.domain i).HoldsC (value i)
  equations : ∀ r ∈ P.relations, r.evalC value = 0

def ctranslate (u a : A) (i : ℕ) := u^i*a*(star u)^i
def cylinder (p : ℕ → A) (M : ℕ) (bits : Fin M → Bool) : A :=
  ((List.finRange M).map (fun j => if bits j then p j else 1-p j)).prod

end
end E2
