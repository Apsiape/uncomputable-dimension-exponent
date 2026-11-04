import E2.CountHolevo
import QIT.Information.Entropy.EntropyTensorPower

/-! Concrete finite CQ families. All zero-mass totalizations are proved harmless. -/
namespace E2.CountCQ
noncomputable section
open scoped BigOperators ComplexOrder NNReal

variable {ι κ b : Type*} [Fintype ι] [Fintype κ] [Fintype b] [DecidableEq b]

structure Family (ι b : Type*) [Fintype ι] [Fintype b] [DecidableEq b] where
  mass : ι → ℝ
  matrix : ι → Matrix b b ℂ
  nonneg : ∀ x, 0 ≤ mass x
  positive : ∀ x, (matrix x).PosSemidef
  trace : ∀ x, (matrix x).trace = (mass x : ℂ)
  total : ∑ x, mass x = 1

namespace Family
variable (F : Family ι b)

theorem matrix_zero {x : ι} (hx : F.mass x = 0) : F.matrix x = 0 := by
  apply (F.positive x).trace_eq_zero_iff.mp
  rw [F.trace, hx, Complex.ofReal_zero]

def normalized (fallback : QIT.State b) (x : ι) : QIT.State b where
  matrix := if F.mass x = 0 then fallback.matrix else (((F.mass x)⁻¹ : ℝ) : ℂ) • F.matrix x
  pos := by
    split_ifs
    · exact fallback.pos
    · convert (F.positive x).smul (inv_nonneg.mpr (F.nonneg x)) using 1
  trace_eq_one := by
    split_ifs with h
    · exact fallback.trace_eq_one
    · rw [Matrix.trace_smul, F.trace]
      simp only [smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ h, Complex.ofReal_one]

theorem mass_normalized (fallback : QIT.State b) (x : ι) :
    (F.mass x : ℂ) • (F.normalized fallback x).matrix = F.matrix x := by
  dsimp only [normalized]
  split_ifs with h
  · simp [h, F.matrix_zero h]
  · rw [smul_smul]
    simp only [← Complex.ofReal_mul, mul_inv_cancel₀ h, Complex.ofReal_one, one_smul]

def ensemble (fallback : QIT.State b) : QIT.Ensemble ι b where
  probs x := NNReal.mk (F.mass x) (F.nonneg x)
  weights_sum := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using F.total
  states := F.normalized fallback

def average : QIT.State b where
  matrix := ∑ x, F.matrix x
  pos := Matrix.posSemidef_sum _ (fun x _ => F.positive x)
  trace_eq_one := by simp only [Matrix.trace_sum, F.trace, ← Complex.ofReal_sum, F.total, Complex.ofReal_one]

theorem ensemble_average (fallback : QIT.State b) : (F.ensemble fallback).averageState = F.average := by
  apply QIT.State.ext
  change (∑ x, (F.mass x : ℂ) • (F.normalized fallback x).matrix) = ∑ x, F.matrix x
  simp only [F.mass_normalized]

def shannon : ℝ := (∑ x, Real.negMulLog (F.mass x)) / Real.log 2

def meanEntropy (fallback : QIT.State b) : ℝ :=
  ∑ x, F.mass x * (F.normalized fallback x).vonNeumann

def conditional (fallback : QIT.State b) : ℝ :=
  F.shannon + F.meanEntropy fallback - F.average.vonNeumann

theorem neg_xlog (x : ℝ) : -QIT.xlog2 x = Real.negMulLog x / Real.log 2 := by
  by_cases hx : x=0
  · simp [hx, Real.negMulLog, QIT.xlog2]
  · simp [Real.negMulLog, QIT.xlog2, QIT.log2, hx, div_eq_mul_inv, mul_assoc]

theorem cq_entropy [DecidableEq ι] (fallback : QIT.State b) :
    (F.ensemble fallback).cqState.vonNeumann = F.shannon + F.meanEntropy fallback := by
  rw [QIT.State.cqState_vonNeumann]
  simp only [ensemble, ← Finset.sum_neg_distrib, neg_xlog, ← Finset.sum_div]
  rfl

theorem cq_entry [DecidableEq ι] (fallback : QIT.State b) (x y : ι) (i j : b) :
    (F.ensemble fallback).cqState.matrix (x,i) (y,j) = if x=y then F.matrix x i j else 0 := by
  by_cases h : x=y
  · subst y
    have he := congrFun (congrFun (QIT.Classical.cqState_block_self (F.ensemble fallback) x) i) j
    change (F.ensemble fallback).cqState.matrix (x,i) (x,j) = ((F.mass x : ℂ) • (F.normalized fallback x).matrix) i j at he
    rw [F.mass_normalized] at he
    simpa only [ite_true] using he
  · have he := congrFun (congrFun (QIT.Classical.cqState_block_ne (E := F.ensemble fallback) h) i) j
    simpa only [QIT.Classical.block, Matrix.zero_apply, ite_eq_right h] using he

def coarse [DecidableEq κ] (f : ι → κ) : Family κ b where
  mass y := ∑ x, if f x=y then F.mass x else 0
  matrix y := ∑ x, if f x=y then F.matrix x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact F.nonneg x; exact le_refl 0)
  positive y := Matrix.posSemidef_sum _ (fun x _ => by split_ifs; exact F.positive x; exact Matrix.PosSemidef.zero)
  trace y := by
    rw [Matrix.trace_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp only [F.trace, Matrix.trace_zero, Complex.ofReal_zero]
  total := by
    rw [Finset.sum_comm]
    simpa using F.total

theorem coarse_average [DecidableEq κ] (f : ι → κ) : (F.coarse f).average = F.average := by
  apply QIT.State.ext
  change (∑ y, ∑ x, if f x=y then F.matrix x else 0) = ∑ x, F.matrix x
  rw [Finset.sum_comm]
  simp

end Family

theorem entropy_matrix_eq {d : ℕ} (s : QIT.State (Fin d)) :
    Companion.Analytic.entropy s.matrix = s.vonNeumann := by
  rw [Companion.Analytic.entropy, dite_eq_left s.pos.isHermitian]
  change (∑ i, Real.negMulLog (s.pos.isHermitian.eigenvalues i))/Real.log 2 =
    -(∑ i, QIT.xlog2 (s.pos.isHermitian.eigenvalues i))
  simp only [← Finset.sum_neg_distrib, Family.neg_xlog, Finset.sum_div]

def original {d : ℕ} (s : E2.State d) : QIT.State (Fin d) := ⟨s.rho,s.positive,s.normalized⟩

def record {d m : ℕ} (s : E2.State d) (p : Fin m → E2.Measurement d) : Family (E2.RecordType p) (Fin d) where
  mass := E2.Turn9.recordMass s p
  matrix := E2.Turn9.recordDensity s p
  nonneg := (E2.record_normalization d m s p).1
  positive := E2.record_density_positive s p
  trace a := by
    have ht := (E2.record_density_positive s p a).isHermitian.trace_eq_sum_eigenvalues
    have hr := E2.record_density_mass s p a
    have hc : (((E2.Turn9.recordDensity s p a).trace.re : ℝ) : ℂ) = (E2.Turn9.recordDensity s p a).trace := by
      rw [ht]
      simp
    rw [← hr]
    exact hc.symm
  total := (E2.record_normalization d m s p).2

theorem record_normalized {d m : ℕ} (s : E2.State d) (p : Fin m → E2.Measurement d) (a : E2.RecordType p) :
    ((record s p).normalized (original s) a).matrix =
      E2.Turn9.normalizedDensity s (E2.Turn9.recordMass s p a) (E2.Turn9.recordDensity s p a) := rfl

theorem record_conditional {d m : ℕ} (s : E2.State d) (p : Fin m → E2.Measurement d) :
    (record s p).conditional (original s) = E2.Turn9.recordEntropy s p + E2.Turn9.recordMeanEntropy s p -
      Companion.Analytic.entropy (E2.Turn9.finalDensity s p) := by
  unfold Family.conditional Family.shannon Family.meanEntropy E2.Turn9.recordMeanEntropy
  simp only [← entropy_matrix_eq, record_normalized]
  rfl

theorem marginal_conditional {d m : ℕ} (s : E2.State d) (p : Fin m → E2.Measurement d) (i : Fin m) :
    ((record s p).coarse (fun a => a i)).conditional (original s) = E2.Turn9.marginalConditionalEntropy s p i := by
  rw [Family.conditional, Family.coarse_average]
  unfold Family.shannon Family.meanEntropy E2.Turn9.marginalConditionalEntropy E2.Turn9.marginalEntropy E2.Turn9.marginalMeanEntropy
  simp only [← entropy_matrix_eq]
  rfl

end
end E2.CountCQ
