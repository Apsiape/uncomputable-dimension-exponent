import E2.MomentFiniteSequence

namespace E2.ExactCompactness
noncomputable section
open Filter
open scoped Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false

theorem source_uniform_near (p : CounterProgram) (hp : RecognizesK p) (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ δ d (m : Model (sourcePresentation p) d δ), 0<δ → δ<η →
      thetaK-ε≤expectation m.state (Poly.eval m.value (sv p 18)) := by
  by_contra! H
  choose δ d m hδ hsmall hcost using (fun n : ℕ => H ((1/2:ℝ)^n) (by positivity))
  have ht : Tendsto δ atTop (nhds 0) := by
    apply squeeze_zero (fun n => (hδ n).le) (fun n => (hsmall n).le)
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  let s : PrecisionSequence (sourcePresentation p) := ⟨d,δ,m,ht⟩
  letI (n : ℕ) : NeZero (s.dimension n) := ⟨Nat.ne_of_gt (s.model n).positive_dimension⟩
  let ms := finiteMomentSequence s
  have hi : 18<sourceSize p := by unfold sourceSize; omega
  have hd := sequenceTuple_domains ms ⟨18,hi⟩
  have hd' : Domain.projection.HoldsC (sequenceTuple ms ⟨18,hi⟩) := by
    simpa [sourcePresentation,sourceDomain] using hd
  have hsa : IsSelfAdjoint ((sv p 18).evalC (sequenceTuple ms)) := by
    change star ((sv p 18).evalC (sequenceTuple ms))=(sv p 18).evalC (sequenceTuple ms)
    simpa only [sv,Poly.evalC_var,Nat.mod_eq_of_lt hi] using hd'.1
  have hu := limit_upper ms (sv p 18) hsa (thetaK-ε) (by
    intro n
    change (matrixStateLinear (m n).state ((sv p 18).evalC (m n).value)).re≤thetaK-ε
    rw [matrix_evalC]
    exact (hcost n).le)
  have hl := ExactForcing.model_flag_density p hp (limitExactModel ms)
  have hl' : thetaK≤((limitExactModel ms).state.toLinearMap ((sv p 18).evalC (limitExactModel ms).value)).re := by
    simpa only [sv,Poly.evalC_var,sourceValue] using hl
  linarith

def shortfalls (p : CounterProgram) (δ : ℝ) : Set ℝ :=
  insert 0 {a | ∃ (d : ℕ) (m : Model (sourcePresentation p) d δ), a=thetaK-expectation m.state (Poly.eval m.value (sv p 18))}

theorem flag_expectation_nonneg {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) : 0≤expectation m.state (Poly.eval m.value (sv p 18)) := by
  have hf : Domain.projection.Holds (Poly.eval m.value (sv p 18)) := by
    simpa [sourceAt,sourceDomain] using sourceAt_domain m 18 (by omega)
  rw [projection_expectation_eq _ _ hf]
  positivity

theorem shortfalls_bdd (p : CounterProgram) (δ : ℝ) : BddAbove (shortfalls p δ) := by
  refine ⟨max 0 thetaK,?_⟩
  intro a ha
  rcases ha with rfl | ⟨d,m,rfl⟩
  · exact le_max_left _ _
  · exact (sub_le_self _ (flag_expectation_nonneg m)).trans (le_max_right _ _)

def flagModulus (p : CounterProgram) (δ : ℝ) : ℝ := sSup (shortfalls p δ)

theorem flagModulus_nonneg (p : CounterProgram) (δ : ℝ) : 0≤flagModulus p δ :=
  le_csSup (shortfalls_bdd p δ) (Set.mem_insert 0 _)

theorem flagModulus_bound (p : CounterProgram) (δ : ℝ) (d : ℕ) (m : Model (sourcePresentation p) d δ) :
    thetaK-flagModulus p δ≤expectation m.state (Poly.eval m.value (sv p 18)) := by
  have h : thetaK-expectation m.state (Poly.eval m.value (sv p 18))≤flagModulus p δ :=
    le_csSup (shortfalls_bdd p δ) (Set.mem_insert_of_mem 0 ⟨d,m,rfl⟩)
  linarith

theorem flagModulus_tendsto (p : CounterProgram) (hp : RecognizesK p) :
    Tendsto (flagModulus p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η,hη,hnear⟩ := source_uniform_near p hp (ε/2) (by linarith)
  have hη' : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ<η :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hη)
  filter_upwards [self_mem_nhdsWithin,hη'] with δ hδ hδη
  have hu : flagModulus p δ≤ε/2 := by
    unfold flagModulus
    apply csSup_le (Set.insert_nonempty 0 _)
    intro a ha
    rcases ha with rfl | ⟨d,m,rfl⟩
    · linarith
    · have hm := hnear δ d m hδ hδη
      linarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (flagModulus_nonneg p δ)]
  linarith

theorem model_uniform_flag_density (p : CounterProgram) (hp : RecognizesK p) :
    ∃ ω : ℝ → ℝ, Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ δ d (m : Model (sourcePresentation p) d δ), 0<δ →
        thetaK-ω δ≤expectation m.state (Poly.eval m.value (sv p 18)) :=
  ⟨flagModulus p,flagModulus_tendsto p hp,fun δ d m _ => flagModulus_bound p δ d m⟩

end
end E2.ExactCompactness
