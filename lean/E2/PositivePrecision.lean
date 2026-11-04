import E2.GameProfileTools

namespace E2
noncomputable section
open scoped BigOperators

 theorem strategy_loss_nonneg {G : BCSGame} {d : ℕ} (s : Strategy G d) : 0 ≤ loss s := by
  rw [BooleanGameLoss.loss_eq_sum]
  apply Finset.sum_nonneg
  intro c hc
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (by exact_mod_cast G.probability_nonneg c v)
    (BooleanGameLoss.localLoss_nonneg s c v)

/-- The value-one premise supplies a terminating witness at every positive
precision; deciding exact finite-dimensional feasibility is a separate step. -/
theorem positive_precision_feasible (G : BCSGame) (hG : quantumValue G = 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ d, Feasible G ε d := by
  classical
  let S := {w : ℝ | ∃ d : ℕ, 0 < d ∧ ∃ s : Strategy G d, winningProbability s = w}
  have hbounded : ∀ w ∈ S, w ≤ 1 := by
    rintro w ⟨d,hd,s,rfl⟩
    exact sub_nonneg.mp (strategy_loss_nonneg s)
  have hbdd : BddAbove S := ⟨1,hbounded⟩
  have hsup : sSup S = 1 := hG
  have hne : S.Nonempty := by
    by_contra hn
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he,Real.sSup_empty] at hsup
    norm_num at hsup
  obtain ⟨w,hw,hl⟩ := exists_lt_of_lt_csSup hne (by rw [hsup]; linarith : 1-ε < sSup S)
  obtain ⟨d,hd,s,rfl⟩ := hw
  exact ⟨d,hd,s,by unfold loss; linarith⟩

 theorem positive_precision_dimension_finite (G : BCSGame) (hG : quantumValue G = 1)
    (ε : ℝ) (hε : 0 < ε) : dimension G ε ≠ ⊤ := by
  obtain ⟨d,hd,s,hs⟩ := positive_precision_feasible G hG ε hε
  exact ProfileTools.game_dimension_finite s hd hs

end
end E2
