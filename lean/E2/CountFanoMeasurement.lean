import E2.CountDataProcessing
import E2.CountFanoScalar
import QIT.Information.Entropy.StrongSubadditivity

namespace E2.CountCQ
noncomputable section
open scoped BigOperators ComplexOrder NNReal

/-- The original projective decoder as a channel to its classical outcome. -/
def decoder {d : ℕ} (p : E2.Measurement d) : QIT.POVM (Fin p.outcomes) (Fin d) where
  effects := p.projection
  pos a := E2.projection_positive ⟨p.selfadjoint a,p.idempotent a⟩
  sum_eq_one := p.complete

namespace Family
variable {d n : ℕ} (F : Family (Fin n) (Fin d)) (P : QIT.POVM (Fin n) (Fin d))

def joint (a b : Fin n) : ℝ := (F.matrix a * P.effects b).trace.re

theorem measure_diagonal (A : Matrix (Fin d) (Fin d) ℂ) :
    (QIT.Channel.measure P).map A = Matrix.diagonal (fun b => (A*P.effects b).trace) := by
  rw [QIT.Channel.measure_map]
  simpa using Matrix.sum_single_eq_diagonal (fun b : Fin n => (A*P.effects b).trace)

theorem joint_nonneg (a b : Fin n) : 0≤F.joint P a b := by
  have h := ((QIT.Channel.measure P).mapsPositive _ (F.positive a)).diag_nonneg (i := b)
  rw [measure_diagonal, Matrix.diagonal_apply_eq] at h
  exact (Complex.nonneg_iff.mp h).1

theorem joint_complex (a b : Fin n) : (F.joint P a b : ℂ) = (F.matrix a*P.effects b).trace := by
  have h := ((QIT.Channel.measure P).mapsPositive _ (F.positive a)).diag_nonneg (i := b)
  rw [measure_diagonal, Matrix.diagonal_apply_eq] at h
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp h).2

theorem joint_row (a : Fin n) : (∑ b,F.joint P a b)=F.mass a := by
  unfold joint
  rw [←Complex.re_sum, ←Matrix.trace_sum, ←Matrix.mul_sum, P.sum_eq_one, Matrix.mul_one, F.trace]
  rfl

theorem joint_total : (∑ b,∑ a,F.joint P a b)=1 := by
  rw [Finset.sum_comm]
  simp only [joint_row, F.total]

theorem measured_conditional (fallback : QIT.State (Fin d)) :
    (F.map (QIT.Channel.measure P)).conditional ((QIT.Channel.measure P).applyState fallback) =
      ((∑ b, ∑ a,Real.negMulLog (F.joint P a b))-
        (∑ b,Real.negMulLog (∑ a,F.joint P a b)))/Real.log 2 := by
  let G := F.map (QIT.Channel.measure P)
  let out := (QIT.Channel.measure P).applyState fallback
  have hcq : (G.ensemble out).cqState.matrix = Matrix.diagonal (fun ab => (F.joint P ab.1 ab.2 : ℂ)) := by
    ext ⟨a,b⟩ ⟨a',b'⟩
    rw [cq_entry]
    change (if a=a' then (QIT.Channel.measure P).map (F.matrix a) b b' else 0) = _
    rw [measure_diagonal]
    by_cases ha : a=a' <;> by_cases hb : b=b' <;> simp [ha,hb,Matrix.diagonal, F.joint_complex]
  have hav : G.average.matrix = Matrix.diagonal (fun b => ((∑ a,F.joint P a b : ℝ):ℂ)) := by
    ext b b'
    change (∑ a,(QIT.Channel.measure P).map (F.matrix a)) b b' = _
    simp only [Matrix.sum_apply, measure_diagonal]
    by_cases hb : b=b'
    · subst b'
      simp only [Matrix.diagonal_apply_eq, Complex.ofReal_sum, F.joint_complex]
    · simp [Matrix.diagonal_apply_ne _ hb]
  have hs := QIT.State.vonNeumann_eq_neg_sum_xlog2_of_diagonal (G.ensemble out).cqState (fun ab => F.joint P ab.1 ab.2) hcq
  have ht := QIT.State.vonNeumann_eq_neg_sum_xlog2_of_diagonal G.average (fun b => ∑ a,F.joint P a b) hav
  rw [← G.cq_conditional out, QIT.State.conditionalEntropy_eq, QIT.Ensemble.cqState_marginalB_eq_averageState, G.ensemble_average, hs, ht]
  simp only [←Finset.sum_neg_distrib, neg_xlog, ←Finset.sum_div, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  ring

theorem fano (hn : n≤3) (fallback : QIT.State (Fin d)) :
    F.conditional fallback ≤ binaryEntropy (∑ b,∑ a∈Finset.univ.erase b,F.joint P a b)+
      (∑ b,∑ a∈Finset.univ.erase b,F.joint P a b) := by
  have hd := F.conditional_dataProcessing (QIT.Channel.measure P) fallback
  rw [F.measured_conditional] at hd
  exact hd.trans (E2.classical_fano_three hn (F.joint P) (F.joint_nonneg P) (F.joint_total P))

end Family
end
end E2.CountCQ
