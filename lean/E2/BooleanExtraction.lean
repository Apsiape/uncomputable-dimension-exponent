import E2.CompilerDefinitions
import E2.CompilerFrontend
import E2.StateConsistencyRectangular
import E2.CarryTools

namespace E2.BooleanExtraction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic E2.CompilerPolynomial

/-- The adjoint-free polynomials supported by a context. -/
def Local {ι : Type*} [DecidableEq ι] (S : Finset ι) : Poly ι → Prop
  | .const _ => True
  | .var i => i ∈ S
  | .add p q => Local S p ∧ Local S q
  | .mul p q => Local S p ∧ Local S q
  | .adj _ => False

theorem eval_consistency {ι : Type*} [DecidableEq ι] {d a : ℕ}
    (hd : 0 < d) (ha : 0 < a) (X : ι → Mat d) (Y : ι → Mat a)
    (Xi : Matrix (Fin d) (Fin a) ℂ) (S : Finset ι) (η : ℝ) (hη : 0 ≤ η)
    (hX : ∀ i, ‖X i‖ ≤ 1) (hY : ∀ i, ‖Y i‖ ≤ 1)
    (hc : ∀ i ∈ S, hs (X i * Xi - Xi * Y i) ≤ η)
    (p : Poly ι) (hp : Local S p) :
    hs (Poly.eval X p * Xi - Xi * Poly.eval Y p) ≤ commBudget p * η := by
  induction p with
  | const q => simp [Poly.eval, commBudget, Matrix.smul_mul, Matrix.mul_smul,
      hs, hsNorm, hsSquared]
  | var i => simpa [Poly.eval, commBudget] using hc i hp
  | add p q ihp ihq =>
    have he : Poly.eval X (.add p q) * Xi - Xi * Poly.eval Y (.add p q) =
        (Poly.eval X p * Xi - Xi * Poly.eval Y p) +
        (Poly.eval X q * Xi - Xi * Poly.eval Y q) := by
      simp only [Poly.eval, Matrix.add_mul, Matrix.mul_add]; abel
    rw [he]
    exact (hsNorm_add_le _ _).trans (by
      simpa only [commBudget, add_mul] using add_le_add (ihp hp.1) (ihq hp.2))
  | mul p q ihp ihq =>
    have he : Poly.eval X (.mul p q) * Xi - Xi * Poly.eval Y (.mul p q) =
        Poly.eval X p * (Poly.eval X q * Xi - Xi * Poly.eval Y q) +
        (Poly.eval X p * Xi - Xi * Poly.eval Y p) * Poly.eval Y q := by
      simp only [Poly.eval, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]; abel
    rw [he]
    calc
      _ ≤ hs (Poly.eval X p * (Poly.eval X q * Xi - Xi * Poly.eval Y q)) +
          hs ((Poly.eval X p * Xi - Xi * Poly.eval Y p) * Poly.eval Y q) := hsNorm_add_le _ _
      _ ≤ ‖Poly.eval X p‖ * hs (Poly.eval X q * Xi - Xi * Poly.eval Y q) +
          hs (Poly.eval X p * Xi - Xi * Poly.eval Y p) * ‖Poly.eval Y q‖ :=
        add_le_add (operator_mul_hs _ _) (hs_mul_operator _ _)
      _ ≤ normBudget p * (commBudget q * η) + (commBudget p * η) * normBudget q := by
        apply add_le_add
        · exact mul_le_mul (eval_norm_bound hd X hX p) (ihq hp.2)
            (hsNorm_nonneg _) (normBudget_nonneg p)
        · exact mul_le_mul (ihp hp.1) (eval_norm_bound ha Y hY q)
            (norm_nonneg _) (mul_nonneg (commBudget_nonneg p) hη)
      _ = commBudget (.mul p q) * η := by simp only [commBudget]; ring
  | adj p ih => exact hp.elim

/-- A rectangular amplitude and its left marginal give the same weighted norm. -/
theorem weighted_eq_amplitude {d a : ℕ} (s : State d)
    (Xi : Matrix (Fin d) (Fin a) ℂ) (hρ : s.rho = Xi * Xi.conjTranspose)
    (R : Mat d) : weighted s R = hs (R * Xi) := by
  have hf {n : ℕ} (Z : Matrix (Fin d) (Fin n) ℂ) :
      hs (R * Z)^2 = (Matrix.trace ((R.conjTranspose * R) * (Z * Z.conjTranspose))).re := by
    rw [hs_square_gram, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  change hs (R * s.xi)^2 = hs (R * Xi)^2
  rw [hf, hf, s.xi_positive.isHermitian.eq, s.xi_square, hρ]

def contextRelations (G : BCSGame) (c : Fin G.contexts) :=
  commList ((G.scope c).toList.map Poly.var) ((G.scope c).toList.map Poly.var) ++
    ((Finset.univ \ G.allowed c).toList.map (assignmentPolynomial G c))

theorem local_assignment (G : BCSGame) (c : Fin G.contexts)
    (a : Fin G.numVars → Bool) : Local (G.scope c) (assignmentPolynomial G c a) := by
  have hh : ∀ v ∈ (G.scope c).toList, Local (G.scope c)
      (Poly.const (1/2) * (1 + (if a v then 1 else -1) * .var v)) := by
    intro v hv
    refine ⟨trivial, trivial, ?_, ?_⟩
    · cases a v <;> trivial
    · simpa only [Local, Finset.mem_toList] using hv
  have fold_local (vs : List (Fin G.numVars))
      (hvs : ∀ v ∈ vs, Local (G.scope c)
        (Poly.const (1/2) * (1 + (if a v then 1 else -1) * .var v))) :
      Local (G.scope c) ((vs.map (fun v =>
        Poly.const (1/2) * (1 + (if a v then 1 else -1) * .var v))).foldr (· * ·) 1) := by
    induction vs with
    | nil => trivial
    | cons v vs ih =>
      exact ⟨hvs v (by simp), ih (fun w hw => hvs w (by simp [hw]))⟩
  exact fold_local _ hh

theorem local_relation (G : BCSGame) (c : Fin G.contexts) (r : Poly (Fin G.numVars))
    (hr : r ∈ contextRelations G c) : Local (G.scope c) r := by
  classical
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_flatMap.mp hr with ⟨p,hp,hr⟩
    rcases List.mem_map.mp hp with ⟨v,hv,rfl⟩
    rcases List.mem_map.mp hr with ⟨q,hq,rfl⟩
    rcases List.mem_map.mp hq with ⟨w,hw,rfl⟩
    have hv' : v ∈ G.scope c := by simpa using hv
    have hw' : w ∈ G.scope c := by simpa using hw
    exact ⟨⟨hv',hw'⟩,⟨trivial,⟨hw',hv'⟩⟩⟩
  · rcases List.mem_map.mp hr with ⟨a,ha,rfl⟩
    exact local_assignment G c a

/-- Exact contextual reflection representations on Alice's side. These are
local representations; no equality between different contexts is assumed. -/
structure ContextRepresentation (G : BCSGame) (a : ℕ) where
  value : Fin G.contexts → Fin G.numVars → Mat a
  domains : ∀ c v, Domain.reflection.Holds (value c v)
  commutes : ∀ c v, v ∈ G.scope c → ∀ w, w ∈ G.scope c →
    value c v * value c w = value c w * value c v
  forbidden : ∀ c b, b ∉ G.allowed c → Poly.eval (value c) (assignmentPolynomial G c b) = 0

theorem ContextRepresentation.relations {G : BCSGame} {a : ℕ}
    (Y : ContextRepresentation G a) (c : Fin G.contexts) (r : Poly (Fin G.numVars))
    (hr : r ∈ contextRelations G c) : Poly.eval (Y.value c) r = 0 := by
  classical
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_flatMap.mp hr with ⟨p,hp,hr⟩
    rcases List.mem_map.mp hp with ⟨v,hv,rfl⟩
    rcases List.mem_map.mp hr with ⟨q,hq,rfl⟩
    rcases List.mem_map.mp hq with ⟨w,hw,rfl⟩
    simpa only [pc, Poly.eval_sub, Poly.eval_mul, Poly.eval_var, sub_eq_zero] using
      Y.commutes c v (by simpa using hv) w (by simpa using hw)
  · rcases List.mem_map.mp hr with ⟨b,hb,rfl⟩
    exact Y.forbidden c b (by simpa using hb)

def extractionConstant (G : BCSGame) : ℝ :=
  1 + Real.sqrt 2 + ((booleanPresentation G).relations.map commBudget).sum

theorem extractionConstant_pos (G : BCSGame) : 0 < extractionConstant G := by
  have hh : 0 ≤ ((booleanPresentation G).relations.map commBudget).sum :=
    List.sum_nonneg (fun b hb => by
      rcases List.mem_map.mp hb with ⟨r,hr,rfl⟩; exact commBudget_nonneg r)
  unfold extractionConstant
  positivity

/-- Complete quantitative extraction after the projective/consistency stage.
All context commutators and forbidden assignment polynomials are controlled;
the supplied state and Bob dimension are preserved. -/
theorem model_of_context_consistency {G : BCSGame} {d a : ℕ}
    (ha : 0 < a) (s : State d) (Xi : Matrix (Fin d) (Fin a) ℂ)
    (hρ : s.rho = Xi * Xi.conjTranspose) (B : Fin G.numVars → Mat d)
    (hB : ∀ v, Domain.reflection.Holds (B v)) (Y : ContextRepresentation G a)
    (η : ℝ) (hη : 0 ≤ η)
    (hc : ∀ c v, v ∈ G.scope c → hs (B v * Xi - Xi * Y.value c v) ≤ η)
    (hu : ∀ v, (∀ c, v ∉ G.scope c) → B v = 1) :
    Nonempty (Model (booleanPresentation G) d (extractionConstant G * η)) := by
  classical
  have hd : 0 < d := state_dimension_pos s
  have hnB v := CompilerFrontend.reflection_norm hd (B v) (hB v)
  have hnY c v := CompilerFrontend.reflection_norm ha (Y.value c v) (Y.domains c v)
  have hsum : 0 ≤ ((booleanPresentation G).relations.map commBudget).sum :=
    List.sum_nonneg (fun b hb => by
      rcases List.mem_map.mp hb with ⟨r,hr,rfl⟩; exact commBudget_nonneg r)
  refine ⟨{
    positive_dimension := hd
    state := s
    value := B
    domains := hB
    defects := ?_
    state_commutators := ?_ }⟩
  · intro r hr
    have hm : r ∈ (List.finRange G.contexts).flatMap (contextRelations G) := hr
    rcases List.mem_flatMap.mp hm with ⟨c,hc',hcr⟩
    rw [weighted_eq_amplitude s Xi hρ]
    have he := eval_consistency hd ha B (Y.value c) Xi (G.scope c) η hη hnB (hnY c)
      (hc c) r (local_relation G c r hcr)
    rw [Y.relations c r hcr, Matrix.mul_zero, sub_zero] at he
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hη
    have ht : commBudget r ≤ ((booleanPresentation G).relations.map commBudget).sum :=
      List.single_le_sum (fun x hx => by
        rcases List.mem_map.mp hx with ⟨q,hq,rfl⟩; exact commBudget_nonneg q)
        (commBudget r) (List.mem_map_of_mem hr)
    dsimp [extractionConstant]
    linarith [Real.sqrt_nonneg (2:ℝ)]
  · intro v
    by_cases hv : ∃ c, v ∈ G.scope c
    · obtain ⟨c,hcv⟩ := hv
      have hh := FiniteTransfer.rectangular_consistency_squared Xi s.xi s.xi_positive
        (s.xi_square.trans hρ) (B v) (Y.value c v) (hB v).1 (Y.domains c v).1
      have he := pow_le_pow_left₀ (hsNorm_nonneg _) (hc c v hcv) 2
      have hbound : hs (comm (B v) s.xi) ≤ Real.sqrt 2 * η := by
        apply (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hη)).mp
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        exact hh.trans (mul_le_mul_of_nonneg_left he (by norm_num))
      apply hbound.trans
      apply mul_le_mul_of_nonneg_right _ hη
      dsimp [extractionConstant]
      linarith
    · rw [hu v (by simpa only [not_exists] using hv)]
      simpa [comm, Companion.Analytic.comm, hs, hsNorm, hsSquared] using
        mul_nonneg (le_of_lt (extractionConstant_pos G)) hη

end
end E2.BooleanExtraction
