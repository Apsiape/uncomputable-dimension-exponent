import E2.BooleanExtraction
import QIT.Util.Matrix

namespace E2.BooleanMixedAmplitude
noncomputable section
open scoped BigOperators ComplexOrder
open Companion.Analytic

abbrev Reference (a d : ℕ) := Fin a × (Fin a × Fin d)

def referenceEquiv (a d : ℕ) : Reference a d ≃ Fin (Fintype.card (Reference a d)) :=
  Fintype.equivFin _

/-- The environment is included in the reference columns, not in Bob's rows. -/
def realign {a d : ℕ} (R : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Matrix (Fin d) (Fin (Fintype.card (Reference a d))) ℂ :=
  fun i j => R (((referenceEquiv a d).symm j).1,i) (((referenceEquiv a d).symm j).2)

theorem realign_gram {a d : ℕ} (R ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hR : R * R.conjTranspose = ρ) :
    realign R * (realign R).conjTranspose = QIT.partialTraceA ρ := by
  ext i j
  change (∑ k, R (((referenceEquiv a d).symm k).1,i) (((referenceEquiv a d).symm k).2) *
      star (R (((referenceEquiv a d).symm k).1,j) (((referenceEquiv a d).symm k).2))) =
    ∑ k : Fin a, ρ (k,i) (k,j)
  calc
    _ = ∑ z : Reference a d, R (z.1,i) z.2 * star (R (z.1,j) z.2) :=
      (referenceEquiv a d).symm.sum_comp _
    _ = ∑ k : Fin a, (R * R.conjTranspose) (k,i) (k,j) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by rw [hR]

def marginalState {a d : ℕ} (ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) : State d where
  rho := QIT.partialTraceA ρ
  positive := QIT.partialTraceA_posSemidef hρ
  normalized := (QIT.partialTraceA_trace ρ).trans htrace
  xi := QIT.psdSqrt (QIT.partialTraceA ρ)
  xi_positive := QIT.psdSqrt_pos _
  xi_square := QIT.psdSqrt_mul_self_of_posSemidef (QIT.partialTraceA_posSemidef hρ)

def amplitude {a d : ℕ} (ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    Matrix (Fin d) (Fin (Fintype.card (Reference a d))) ℂ := realign (QIT.psdSqrt ρ)

theorem amplitude_gram {a d : ℕ} (ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) :
    (marginalState ρ hρ htrace).rho = amplitude ρ * (amplitude ρ).conjTranspose := by
  symm
  apply realign_gram
  rw [(QIT.psdSqrt_isHermitian ρ).eq,QIT.psdSqrt_mul_self_of_posSemidef hρ]

/-- Every Bob residual has exactly the original mixed-marginal weighted norm. -/
theorem weighted_eq_amplitude {a d : ℕ}
    (ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) (R : Mat d) :
    weighted (marginalState ρ hρ htrace) R = hs (R * amplitude ρ) :=
  BooleanExtraction.weighted_eq_amplitude _ _ (amplitude_gram ρ hρ htrace) R

end
end E2.BooleanMixedAmplitude
