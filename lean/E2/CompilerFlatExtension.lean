import E2.CompilerFlat
import E2.CompilerRealification

namespace E2.CompilerRealification
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Companion.Analytic E2.CompilerBlocks E2.FiniteConstruction
variable {d : ℕ}

/-- Reindexing only permutes diagonal entries. -/
theorem trace_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix α α ℂ) :
    (matrixReindexStar e M).trace = M.trace := by
  change (∑ i : β, M (e.symm i) (e.symm i)) = ∑ i : α, M i i
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- Trace formula for the actual finite-dimensional block flattening. -/
theorem trace_double (M : Block (Mat d)) :
    (doubleMatrix M).trace = (M 0 0).trace + (M 1 1).trace := by
  rw [doubleMatrix,trace_reindex]
  simp [Matrix.trace,Matrix.diag,flatten,Fintype.sum_prod_type,Fin.sum_univ_two]

/-- Complex trace becomes twice its real part. -/
theorem trace_realify (M : Mat d) :
    (realify M).trace = (2 : ℂ) * (M.trace.re : ℂ) := by
  rw [realify,trace_double]
  simp [block,realPart,Matrix.trace,Matrix.diag,Complex.re_sum]
  ring

/-- Exact Hilbert--Schmidt scaling, with no dimension-dependent estimate. -/
theorem hs_realify_square (M : Mat d) : hs (realify M)^2 = 2 * hs M^2 := by
  rw [hsNorm_sq,hsSquared_trace,hsNorm_sq,hsSquared_trace]
  change ((star (realify M) * realify M).trace).re = _
  rw [← realify_star,← realify_mul,trace_realify]
  simp [Matrix.star_eq_conjTranspose]

/-- Realification preserves the normalized flat norm exactly. -/
theorem weighted_realify (hd : 0<d) (M : Mat d) :
    weighted (flatState (2*d) (by omega)) (realify M) = weighted (flatState d hd) M := by
  have he : weighted (flatState (2*d) (by omega)) (realify M)^2 =
      weighted (flatState d hd) M^2 := by
    rw [CompilerFlat.flat_state_weighted_square,CompilerFlat.flat_state_weighted_square,
      hs_realify_square]
    push_cast
    field_simp
  exact (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp he

/-- A complete flat model is transported, preserving every error bound. -/
def flatRealifyModel {ι : Type*} {P : Presentation ι} {δ : ℝ}
    (m : Model P d δ) (hδ : 0≤δ) (hm : m.Flat) : Model P (2*d) δ where
  positive_dimension := by have := m.positive_dimension; omega
  state := flatState (2*d) (by have := m.positive_dimension; omega)
  value i := realify (m.value i)
  domains i := realify_domain _ _ (m.domains i)
  defects p hp := by
    rw [eval_realify,weighted_realify m.positive_dimension]
    rw [← CompilerFlat.flat_model_state m hm]
    exact m.defects p hp
  state_commutators i := by simpa [flatState_commutes,hs,hsNorm,hsSquared] using hδ

theorem flatRealifyModel_flat {ι : Type*} {P : Presentation ι} {δ : ℝ}
    (m : Model P d δ) (hδ : 0≤δ) (hm : m.Flat) :
    (flatRealifyModel m hδ hm).Flat := by
  simp [Model.Flat,flatRealifyModel,flatState,one_div]

end
end E2.CompilerRealification
