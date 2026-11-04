import E2.CompilerFrontend
import E2.CarryTools

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator

structure IdealTerm {ι : Type*} (P : Presentation ι) where
  left : Poly ι
  relation : Poly ι
  relation_mem : relation ∈ P.relations
  adjoint : Bool
  right : Poly ι

def IdealTerm.polynomial {ι : Type*} {P : Presentation ι} (t : IdealTerm P) : Poly ι :=
  t.left * (if t.adjoint then t.relation.adj else t.relation) * t.right

/-- A checkable finite algebraic identity, not an assumed closure principle. -/
structure IdealCertificate {ι : Type*} (P : Presentation ι) (p : Poly ι) where
  terms : List (IdealTerm P)
  identity : ∀ (d : ℕ) (x : ι → Mat d),
    Poly.eval x p = (terms.map (fun t => Poly.eval x t.polynomial)).sum

namespace IdealCertificate
open CompilerPolynomial

/-- Translate each original certificate summand to a checked derivation. -/
def termDerivation {ι : Type*} {P : Presentation ι} (t : IdealTerm P) :
    Derivation P.relations t.polynomial := by
  cases h : t.adjoint
  · simpa only [IdealTerm.polynomial,h,Bool.false_eq_true,ite_false] using
      Derivation.right t.right (Derivation.left t.left (.base t.relation t.relation_mem))
  · simpa only [IdealTerm.polynomial,h,ite_true] using
      Derivation.right t.right (Derivation.left t.left (.adj (.base t.relation t.relation_mem)))

def sumPolynomial {ι : Type*} {P : Presentation ι} : List (IdealTerm P) → Poly ι
  | [] => 0
  | t :: ts => t.polynomial + sumPolynomial ts

def sumDerivation {ι : Type*} {P : Presentation ι} (ts : List (IdealTerm P)) :
    Derivation P.relations (sumPolynomial ts) :=
  match ts with
  | [] => .zero
  | t :: ts => .add (termDerivation t) (sumDerivation ts)

theorem eval_sumPolynomial {ι : Type*} {P : Presentation ι} (ts : List (IdealTerm P))
    (d : ℕ) (x : ι → Mat d) :
    Poly.eval x (sumPolynomial ts) = (ts.map (fun t => Poly.eval x t.polynomial)).sum := by
  induction ts with
  | nil => simp [sumPolynomial]
  | cons t ts ih => simp [sumPolynomial,ih]

def derivation {ι : Type*} {P : Presentation ι} {p : Poly ι} (cert : IdealCertificate P p) :
    Derivation P.relations p :=
  .equal (sumDerivation cert.terms) (fun d x =>
    (eval_sumPolynomial cert.terms d x).trans (cert.identity d x).symm)

end IdealCertificate

/-- Last assertion of Lemma 2.2, with the fixed derivation as finite data. -/
theorem weighted_ideal_derivation {ι : Type*} (P : Presentation ι) (p : Poly ι)
    (cert : IdealCertificate P p) : ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (δ : ℝ) (m : Model P d δ), 0 ≤ δ → weighted m.state (Poly.eval m.value p) ≤ C*δ := by
  let D := cert.derivation
  refine ⟨D.cost + 1, by have := D.cost_nonneg; linarith, ?_⟩
  intro d δ m hδ
  have hn (i : ι) : ‖m.value i‖ ≤ 1 := by
    have hi := m.domains i
    cases h : P.domain i with
    | positiveContraction => exact positive_contraction_norm (h ▸ hi)
    | projection => exact projection_norm_le (h ▸ hi)
    | reflection => exact CompilerFrontend.reflection_norm m.positive_dimension _ (h ▸ hi)
    | unitary => exact (unitary_norm m.positive_dimension (h ▸ hi)).le
  exact (D.weighted_bound m.state m.positive_dimension m.value δ hδ hn
    m.state_commutators m.defects).trans (by nlinarith)

end
end E2
