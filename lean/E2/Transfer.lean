import E2.Compiler
import E2.Lower
import E2.Finite
import E2.StateConsistencyRectangular
import E2.BooleanStrategyBridge
import E2.SourceProfiles
import E2.GameExponent

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator

/-- Lemma 10.2, with rectangular amplitude and the actual marginal square root. -/
theorem consistency_sqrt_state (d a : ℕ) (B : Mat d) (A : Mat a)
    (Xi : Matrix (Fin d) (Fin a) ℂ) (s : State d) (η : ℝ)
    (hB : Domain.reflection.Holds B) (hA : Domain.reflection.Holds A)
    (hρ : s.rho=Xi*Xi.conjTranspose) (hη : hs (B*Xi-Xi*A) ≤ η) :
    hs (comm B s.xi) ≤ Real.sqrt 2*η := by
  have hh := FiniteTransfer.rectangular_consistency_squared Xi s.xi s.xi_positive
    (s.xi_square.trans hρ) B A hB.1 hA.1
  have hη0 : 0 ≤ η := (Companion.Analytic.hsNorm_nonneg _).trans hη
  have hsquare := pow_le_pow_left₀ (Companion.Analytic.hsNorm_nonneg _) hη 2
  apply (sq_le_sq₀ (Companion.Analytic.hsNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hη0)).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact hh.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))

/-- Direct local-dimension extraction for an ordinary Boolean game. No
unverified adaptation of the cited return theorem is accepted as a hypothesis. -/
theorem boolean_extraction (G : BCSGame) :
    ∃ c : ℕ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ε : ℝ) (d : ℕ) (s : Strategy G d), 0 ≤ ε → loss s ≤ ε →
        ∃ d', d' ≤ c*d ∧ Nonempty (Model (booleanPresentation G) d' (C*Real.sqrt ε)) := by
  obtain ⟨c,hc,K,hK,hbridge⟩ := BooleanExtraction.strategyConsistencyBridge G
  refine ⟨c,hc,BooleanExtraction.extractionConstant G * K,
    mul_pos (BooleanExtraction.extractionConstant_pos G) hK,?_⟩
  intro ε d s hε hs
  obtain ⟨w⟩ := hbridge ε d s hε hs
  refine ⟨w.localDimension,w.dimension_bound,?_⟩
  simpa only [mul_assoc] using w.model
    (mul_nonneg hK.le (Real.sqrt_nonneg ε))

def TwoTransfers {ι : Type*} (P : Presentation ι) (G : BCSGame) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    (∀ (ε : ℝ) (d : ℕ) (s : Strategy G d), 0 ≤ ε → loss s ≤ ε →
      ∃ d', d' ≤ c*d ∧ Nonempty (Model P d' (C*Real.sqrt ε))) ∧
    (∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0 ≤ δ → m.Flat →
      ∃ d', 0 < d' ∧ d' ≤ c*d ∧ ∃ s : Strategy G d', loss s ≤ C*δ^2)

/-- Proposition 10.3; fixed constants are shared between both directions. -/
theorem game_transfers : TwoTransfers PK contextGame := by
  obtain ⟨c,hc,C,hC,extract⟩ := boolean_extraction contextGame
  let cp := compiledSource
  refine ⟨max c cp.dimensionFactor, lt_of_lt_of_le hc (le_max_left _ _),
    max (cp.errorFactor*C) cp.errorFactor,
    lt_of_lt_of_le cp.error_pos (le_max_right _ _), ?_, ?_⟩
  · intro ε d s hε hs
    obtain ⟨d',hd',⟨b⟩⟩ := extract ε d s hε hs
    obtain ⟨out,hstate⟩ := cp.soundness (C*Real.sqrt ε) d' b
      (mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg _))
    have hprec : cp.errorFactor*(C*Real.sqrt ε) ≤
        max (cp.errorFactor*C) cp.errorFactor*Real.sqrt ε := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    exact ⟨d',hd'.trans (Nat.mul_le_mul_right d (le_max_left _ _)),⟨out.weaken hprec⟩⟩
  · intro δ d m hδ hm
    obtain ⟨d',hdpos,hd',s,hs⟩ := cp.completeness δ d m hδ hm
    exact ⟨d',hdpos,hd'.trans (Nat.mul_le_mul_right d (le_max_right _ _)),s,
      hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg δ))⟩

def ProfileSlope (D : ℝ → ℕ∞) (slope : ℝ) : Prop :=
  (∀ δ, 0 < δ → D δ ≠ ⊤) ∧
    Filter.Tendsto (fun δ => Real.logb 2 ((D δ).toNat:ℝ) / Real.logb 4 (1/δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds slope)

/-- The monotonic interpolation and logarithmic estimates in Corollary 10.1. -/
theorem profiles_of_model_estimates (p : CounterProgram)
    (hlower : UniformLower (sourcePresentation p) (3+thetaK))
    (hfinite : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → Even N →
      ∃ k : ℕ, |(k:ℝ)-thetaN p N*N| ≤ C*Real.logb 2 (N+2) ∧
        ∃ m : Model (sourcePresentation p) (2^(3*N+k)) (3*(4:ℝ)^(-(N:ℤ))),
          m.Flat ∧ ∀ r ∈ (sourcePresentation p).relations,
            ‖Poly.eval m.value r‖ ≤ 3*(4:ℝ)^(-(N:ℤ)))
    (hlimit : Filter.Tendsto (thetaN p) Filter.atTop (nhds thetaK)) :
    ProfileSlope (W (sourcePresentation p)) (3+thetaK) ∧
      ProfileSlope (H (sourcePresentation p)) (3+thetaK) := by
  exact ⟨ProfileTools.source_profile p hlower hfinite hlimit false,
    ProfileTools.source_profile p hlower hfinite hlimit true⟩

/-- Corollary 10.1, assembled from Sections 7 and 9. -/
theorem matched_source_profiles :
    ProfileSlope (W PK) (3+thetaK) ∧ ProfileSlope (H PK) (3+thetaK) := by
  exact profiles_of_model_estimates recognizer
    (arbitrary_state_lower recognizer recognizer_correct)
    (simultaneous_finite_models recognizer recognizer_correct)
    (finite_flag_limit recognizer recognizer_correct).2

def comparisonSequence (p : CounterProgram) (N : ℕ) : ℤ := 3*N + ⌊N*thetaN p N⌋

/-- Computable comparison sequence in Corollary 10.1. -/
theorem matched_comparison : Computable (comparisonSequence recognizer) ∧
    Filter.Tendsto (fun N : ℕ =>
      (Real.logb 2 ((W PK ((4:ℝ)^(-(N:ℤ)))).toNat : ℝ)-comparisonSequence recognizer N)/N)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun N : ℕ =>
      (Real.logb 2 ((H PK ((4:ℝ)^(-(N:ℤ)))).toNat : ℝ)-comparisonSequence recognizer N)/N)
      Filter.atTop (nhds 0) := by
  sorry

/-- The final analytic game conclusion, with its substantive inputs exposed.
Monotonic interpolation gives the limit for every real epsilon decreasing to 0. -/
theorem game_exponent_of_profiles {ι : Type*} (P : Presentation ι) (G : BCSGame)
    (htrans : TwoTransfers P G)
    (hprofiles : ProfileSlope (W P) (3+thetaK) ∧ ProfileSlope (H P) (3+thetaK))
    (hlower : UniformLower P (3+thetaK)) :
    quantumValue G = 1 ∧ NoPerfectStrategy G ∧ DimensionExponent G betaK := by
  obtain ⟨c,hc,C,hC,hsound,hcomplete⟩ := htrans
  exact ProfileTools.game_conclusions P G c hc C hC hsound hcomplete
    hprofiles.1.1 hprofiles.1.2 hprofiles.2.1 hprofiles.2.2 hlower

end
end E2
