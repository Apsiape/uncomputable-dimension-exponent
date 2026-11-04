import E2.CompilerCertificates
import E2.PolyEval
import E2.MatrixFunctions

namespace E2.CompilerPolynomial
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic
universe u
variable {ι : Type u}

def normBudget : Poly ι → ℝ
  | .const q => ‖(q : ℂ)‖
  | .var _ => 1
  | .add p q => normBudget p + normBudget q
  | .mul p q => normBudget p * normBudget q
  | .adj p => normBudget p

def commBudget : Poly ι → ℝ
  | .const _ => 0
  | .var _ => 1
  | .add p q => commBudget p + commBudget q
  | .mul p q => normBudget p * commBudget q + commBudget p * normBudget q
  | .adj p => commBudget p

theorem normBudget_nonneg (p : Poly ι) : 0 ≤ normBudget p := by
  induction p <;> simp only [normBudget] <;> positivity

theorem commBudget_nonneg (p : Poly ι) : 0 ≤ commBudget p := by
  induction p with
  | const q => exact le_rfl
  | var i => norm_num [commBudget]
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq =>
    exact add_nonneg (mul_nonneg (normBudget_nonneg p) hq) (mul_nonneg hp (normBudget_nonneg q))
  | adj p hp => exact hp

theorem eval_norm_bound {d : ℕ} (hd : 0 < d) (x : ι → Mat d)
    (hx : ∀ i, ‖x i‖ ≤ 1) (p : Poly ι) : ‖Poly.eval x p‖ ≤ normBudget p := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  induction p with
  | const q => simp [Poly.eval, normBudget, norm_smul]
  | var i => exact hx i
  | add p q hp hq => exact (norm_add_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
    exact (norm_mul_le _ _).trans (mul_le_mul hp hq (norm_nonneg _) (normBudget_nonneg p))
  | adj p hp =>
    simpa only [Poly.eval, normBudget, ← Matrix.star_eq_conjTranspose, norm_star] using hp

theorem adjoint_commutator {d : ℕ} (s : State d) (A : Mat d) :
    hs (comm A.conjTranspose s.xi) = hs (comm A s.xi) := by
  have he : comm A.conjTranspose s.xi = -(comm A s.xi).conjTranspose := by
    simp only [comm, Companion.Analytic.comm, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq]
    abel
  rw [he,hs_neg_matrix]
  exact hsNorm_conjTranspose _

theorem eval_comm_bound {d : ℕ} (s : State d) (hd : 0 < d)
    (x : ι → Mat d) (η : ℝ) (hη : 0 ≤ η)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hc : ∀ i, hs (comm (x i) s.xi) ≤ η)
    (p : Poly ι) : hs (comm (Poly.eval x p) s.xi) ≤ commBudget p * η := by
  induction p with
  | const q =>
    simp [Poly.eval, commBudget, comm, Companion.Analytic.comm,
      Matrix.mul_smul,Matrix.smul_mul,hs,hsNorm,hsSquared]
  | var i => simpa [Poly.eval, commBudget] using hc i
  | add p q hp hq =>
    have he : comm (Poly.eval x (.add p q)) s.xi =
        comm (Poly.eval x p) s.xi + comm (Poly.eval x q) s.xi := by
      simp only [Poly.eval,comm,Companion.Analytic.comm,Matrix.add_mul,Matrix.mul_add]
      abel
    rw [he]
    exact (hsNorm_add_le _ _).trans (by simpa [commBudget,add_mul] using add_le_add hp hq)
  | mul p q hp hq =>
    rw [Poly.eval,comm_mul_left]
    calc
      _ ≤ hs (Poly.eval x p*comm (Poly.eval x q) s.xi) +
        hs (comm (Poly.eval x p) s.xi*Poly.eval x q) := hsNorm_add_le _ _
      _ ≤ ‖Poly.eval x p‖*hs (comm (Poly.eval x q) s.xi) +
        hs (comm (Poly.eval x p) s.xi)*‖Poly.eval x q‖ :=
        add_le_add (operator_mul_hs _ _) (hs_mul_operator _ _)
      _ ≤ normBudget p*(commBudget q*η) + (commBudget p*η)*normBudget q := by
        apply add_le_add
        · exact mul_le_mul (eval_norm_bound hd x hx p) hq (hsNorm_nonneg _) (normBudget_nonneg p)
        · exact mul_le_mul hp (eval_norm_bound hd x hx q) (norm_nonneg _)
            (mul_nonneg (commBudget_nonneg p) hη)
      _ = commBudget (.mul p q)*η := by simp only [commBudget]; ring
  | adj p hp => simpa only [Poly.eval,commBudget,adjoint_commutator] using hp

/-- A finite *-ideal derivation with checked semantic equality steps. A
certificate can only use original relations and the displayed algebra rules. -/
inductive Derivation (relations : List (Poly ι)) : Poly ι → Type u
  | base (p : Poly ι) : p ∈ relations → Derivation relations p
  | zero : Derivation relations 0
  | add {p q : Poly ι} : Derivation relations p → Derivation relations q → Derivation relations (p+q)
  | scale (c : ℚ) {p : Poly ι} : Derivation relations p → Derivation relations (.const c*p)
  | left (a : Poly ι) {p : Poly ι} : Derivation relations p → Derivation relations (a*p)
  | right (a : Poly ι) {p : Poly ι} : Derivation relations p → Derivation relations (p*a)
  | adj {p : Poly ι} : Derivation relations p → Derivation relations p.adj
  | equal {p q : Poly ι} : Derivation relations p →
      (∀ (d : ℕ) (x : ι → Mat d), Poly.eval x p = Poly.eval x q) → Derivation relations q

def Derivation.cost {relations : List (Poly ι)} {p : Poly ι} : Derivation relations p → ℝ
  | .base _ _ => 1
  | .zero => 0
  | .add D E => D.cost+E.cost
  | .scale c D => ‖(c : ℂ)‖*D.cost
  | .left a D => normBudget a*D.cost
  | .right a (p := p) D => normBudget a*D.cost+normBudget p*commBudget a
  | .adj (p := p) D => D.cost+commBudget p
  | .equal D _ => D.cost

theorem Derivation.cost_nonneg {relations : List (Poly ι)} {p : Poly ι}
    (D : Derivation relations p) : 0 ≤ D.cost := by
  induction D with
  | base p hp => norm_num [Derivation.cost]
  | zero => exact le_rfl
  | add D E hD hE => exact add_nonneg hD hE
  | scale c D hD => exact mul_nonneg (norm_nonneg _) hD
  | left a D hD => exact mul_nonneg (normBudget_nonneg a) hD
  | @right a p D hD =>
    exact add_nonneg (mul_nonneg (normBudget_nonneg a) hD)
      (mul_nonneg (normBudget_nonneg p) (commBudget_nonneg a))
  | @adj p D hD => exact add_nonneg hD (commBudget_nonneg p)
  | equal D he hD => exact hD

/-- Dimension-independent linear weighted soundness of every finite algebraic
certificate. The state is neither replaced nor enlarged. -/
theorem Derivation.weighted_bound {relations : List (Poly ι)} {p : Poly ι}
    (D : Derivation relations p) {d : ℕ} (s : State d) (hd : 0 < d)
    (x : ι → Mat d) (η : ℝ) (hη : 0 ≤ η)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hc : ∀ i, hs (comm (x i) s.xi) ≤ η)
    (hrel : ∀ r ∈ relations, weighted s (Poly.eval x r) ≤ η) :
    weighted s (Poly.eval x p) ≤ D.cost*η := by
  induction D with
  | base p hp => simpa [Derivation.cost] using hrel p hp
  | zero => simp [Derivation.cost]
  | add D E hD hE =>
    exact (weighted_add s _ _).trans (by simpa [Derivation.cost,add_mul] using add_le_add hD hE)
  | scale c D hD =>
    simp only [Poly.eval, Matrix.smul_mul, Matrix.one_mul,CompilerCertificates.weighted_smul]
    simpa only [Derivation.cost,mul_assoc] using mul_le_mul_of_nonneg_left hD (norm_nonneg (c : ℂ))
  | left a D hD =>
    apply (weighted_left s _ _).trans
    simpa only [Derivation.cost,mul_assoc] using
      mul_le_mul (eval_norm_bound hd x hx a) hD (hsNorm_nonneg _) (normBudget_nonneg a)
  | @right a p D hD =>
    apply (weighted_right s _ _).trans
    calc
      _ ≤ normBudget a*(D.cost*η) + normBudget p*(commBudget a*η) := by
        apply add_le_add
        · exact mul_le_mul (eval_norm_bound hd x hx a) hD (hsNorm_nonneg _) (normBudget_nonneg a)
        · exact mul_le_mul (eval_norm_bound hd x hx p) (eval_comm_bound s hd x η hη hx hc a)
            (hsNorm_nonneg _) (normBudget_nonneg p)
      _ = _ := by simp only [Derivation.cost]; ring
  | @adj p D hD =>
    apply (weighted_adjoint s _).trans
    simpa only [Derivation.cost,add_mul] using add_le_add hD (eval_comm_bound s hd x η hη hx hc p)
  | equal D he hD => simpa only [← he d x, Derivation.cost] using hD

end
end E2.CompilerPolynomial
