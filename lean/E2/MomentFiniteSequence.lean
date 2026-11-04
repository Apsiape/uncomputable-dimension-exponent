import E2.MomentLimitModel
import E2.MomentMatrixStates

namespace E2.ExactCompactness
noncomputable section
open Filter
open scoped ENNReal Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
variable {ι : Type*}



structure PrecisionSequence (P : Presentation ι) where
  dimension : ℕ → ℕ
  precision : ℕ → ℝ
  model : ∀ n, Model P (dimension n) (precision n)
  tends : Tendsto precision atTop (nhds 0)



theorem matrix_evalC {d : ℕ} (x : ι → Mat d) (r : Poly ι) : r.evalC x=Poly.eval x r := by
  induction r <;> simp_all only [Poly.evalC,Poly.eval,Matrix.star_eq_conjTranspose]



def finiteMomentSequence {P : Presentation ι} (s : PrecisionSequence P) [∀ n, NeZero (s.dimension n)] : MomentSequence P (fun n => Mat (s.dimension n)) where
  functional n := matrixStateLinear (s.model n).state
  bounded n := matrixState_bound (s.model n).state
  hermitian n := matrixState_star (s.model n).state
  positive n a := by rw [matrixState_square]; positivity
  normalized n := matrixState_one (s.model n).state
  tuple n := (s.model n).value
  tuple_norm n j := matrix_domain_norm (s.model n).positive_dimension _ _ ((s.model n).domains j)
  domains n j := matrix_domain_to_exact _ _ ((s.model n).domains j)
  central j a := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) _ (by simpa using (s.tends.const_mul (2*‖a‖)))
    intro n
    calc
      _≤2*hs (comm ((s.model n).value j) (s.model n).state.xi)*‖a n‖ := matrixState_cyclic_error _ _ _
      _≤(2*‖a‖)*s.precision n := by
        have hc := (s.model n).state_commutators j
        have hn := lp.norm_apply_le_norm ENNReal.top_ne_zero a n
        have h0 : 0≤hs (comm ((s.model n).value j) (s.model n).state.xi) := Companion.Analytic.hsNorm_nonneg _
        have hp : 0≤s.precision n := h0.trans hc
        nlinarith [norm_nonneg (a n),norm_nonneg a,mul_le_mul hc hn (norm_nonneg (a n)) hp]
  relations r hr := by
    let w := fun n => weighted (s.model n).state (Poly.eval (s.model n).value r)
    have hw : ∀ n, 0≤w n := fun n => Companion.Analytic.hsNorm_nonneg _
    have hb : ∀ n, w n≤s.precision n := fun n => (s.model n).defects r hr
    have ht : Tendsto (fun n => w n^2) atTop (nhds 0) := by
      apply squeeze_zero (fun n => sq_nonneg _) (fun n => pow_le_pow_left₀ (hw n) (hb n) 2)
      simpa using s.tends.pow 2
    have ht' := Complex.continuous_ofReal.tendsto 0 |>.comp ht
    simpa only [matrixState_square_complex,matrix_evalC,Complex.ofReal_zero,w,Function.comp_def] using ht'



def finiteLimitModel {P : Presentation ι} (s : PrecisionSequence P) [∀ n, NeZero (s.dimension n)] := limitExactModel (finiteMomentSequence s)




end
end E2.ExactCompactness
