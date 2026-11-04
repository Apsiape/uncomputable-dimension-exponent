import E2.CompilerDomains
import E2.CompilerPolynomial

namespace E2.CompilerFrontend
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerPolynomial
open Companion.Analytic
variable {ι κ : Type*}

def substitute (replacement : ι → Poly κ) : Poly ι → Poly κ
  | .const q => .const q
  | .var i => replacement i
  | .add p q => substitute replacement p + substitute replacement q
  | .mul p q => substitute replacement p * substitute replacement q
  | .adj p => (substitute replacement p).adj

theorem eval_substitute {d : ℕ} (replacement : ι → Poly κ) (x : κ → Mat d) (p : Poly ι) :
    Poly.eval x (substitute replacement p)=Poly.eval (fun i => Poly.eval x (replacement i)) p := by
  induction p <;> simp_all [substitute,Poly.eval]

def unitaryWord (i : ι) : Poly (ι × Fin 2) := .var (i,0) * .var (i,1)

def replacement (P : Presentation ι) (i : ι) : Poly (ι × Fin 2) :=
  match P.domain i with
  | .reflection => .var (i,0)
  | .projection => .const (1/2) * (1+.var (i,0))
  | .unitary => unitaryWord i
  | .positiveContraction => .const (1/4) * (1+1+unitaryWord i+(unitaryWord i).adj)

def reflectionPresentation (P : Presentation ι) : Presentation (ι × Fin 2) where
  domain _ := .reflection
  relations := P.relations.map (substitute (replacement P))

theorem replacement_domain {d : ℕ} (P : Presentation ι) (x : ι × Fin 2 → Mat d)
    (hx : ∀ j, Domain.reflection.Holds (x j)) (i : ι) :
    (P.domain i).Holds (Poly.eval x (replacement P i)) := by
  have hu := CompilerDomains.reflection_product_unitary (x (i,0)) (x (i,1)) (hx _) (hx _)
  generalize hD : P.domain i = D
  cases D with
  | reflection => simpa [replacement,hD,Poly.eval] using hx (i,0)
  | projection =>
    simpa [replacement,hD,Poly.eval,CompilerDomains.decodeProjection] using
      CompilerDomains.decode_projection (x (i,0)) (hx (i,0))
  | unitary => simpa [replacement,hD,unitaryWord,Poly.eval] using hu
  | positiveContraction =>
    simpa [replacement,hD,unitaryWord,Poly.eval,CompilerDomains.decodePositive] using
      CompilerDomains.decode_positive (x (i,0)*x (i,1)) hu

theorem reflection_norm {d : ℕ} (hd : 0 < d) (R : Mat d)
    (hR : Domain.reflection.Holds R) : ‖R‖ ≤ 1 := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have hs : ‖R‖*‖R‖=1 := by
    rw [← CStarRing.norm_star_mul_self (x:=R),Matrix.star_eq_conjTranspose,hR.1,hR.2]
    exact norm_one
  nlinarith [norm_nonneg R]

/-- The all-reflection front end has exact source domains and same-space,
same-state linear soundness, for the original unrestricted presentation. -/
theorem reflection_frontend_soundness [Fintype ι] (P : Presentation ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : ℝ) (d : ℕ)
      (m : Model (reflectionPresentation P) d η), 0 ≤ η →
      ∃ out : Model P d (C*η), out.state=m.state := by
  classical
  let C : ℝ := 1+∑ i, commBudget (replacement P i)
  have hsum : 0 ≤ ∑ i, commBudget (replacement P i) :=
    Finset.sum_nonneg (fun i _ => commBudget_nonneg _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,by linarith,?_⟩
  intro η d m hη
  have hx (j : ι × Fin 2) : Domain.reflection.Holds (m.value j) := m.domains j
  have hn (j : ι × Fin 2) : ‖m.value j‖ ≤ 1 := reflection_norm m.positive_dimension _ (hx j)
  have hprec : η ≤ C*η := by nlinarith
  let out : Model P d (C*η) := {
    positive_dimension := m.positive_dimension
    state := m.state
    value := fun i => Poly.eval m.value (replacement P i)
    domains := replacement_domain P m.value hx
    defects := by
      intro r hr
      have hb := m.defects (substitute (replacement P) r) (List.mem_map_of_mem hr)
      apply le_trans ?_ hprec
      simpa only [eval_substitute] using hb
    state_commutators := by
      intro i
      have hb := eval_comm_bound m.state m.positive_dimension m.value η hη hn m.state_commutators
        (replacement P i)
      apply hb.trans
      apply mul_le_mul_of_nonneg_right _ hη
      have hi := Finset.single_le_sum (fun j _ => commBudget_nonneg (replacement P j))
        (Finset.mem_univ i)
      dsimp [C]
      linarith }
  exact ⟨out,rfl⟩

end
end E2.CompilerFrontend
