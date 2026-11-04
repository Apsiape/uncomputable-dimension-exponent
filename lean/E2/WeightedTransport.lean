import E2.HSFunctionalCalculus
import E2.RawWords

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator
open Companion.Analytic

/-- Unitary transport pays the state commutator once, against the operator
norm of the accumulated error. No Lipschitz constant multiplies old error. -/
theorem unitary_weighted_transport {d : ℕ} (s : State d) (V E : Mat d)
    (hV : Domain.unitary.Holds V) :
    weighted s (V.conjTranspose*E*V) ≤ weighted s E+‖E‖*hs (comm V s.xi) := by
  have he : V.conjTranspose*E*V*s.xi=
      V.conjTranspose*(E*s.xi)*V+V.conjTranspose*(E*comm V s.xi) := by
    simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  have hu : (V.conjTranspose).conjTranspose*V.conjTranspose=1 := by simpa using hV.2
  have hfirst : hs (V.conjTranspose*(E*s.xi)*V)=hs (E*s.xi) :=
    hs_biunitary V V hV hV _
  have hsecond : hs (V.conjTranspose*(E*comm V s.xi))=hs (E*comm V s.xi) :=
    hsNorm_unitary_left _ _ hu
  unfold weighted
  rw [he]
  calc
    _ ≤ hs (V.conjTranspose*(E*s.xi)*V)+hs (V.conjTranspose*(E*comm V s.xi)) := hsNorm_add_le _ _
    _ = hs (E*s.xi)+hs (E*comm V s.xi) := by rw [hfirst,hsecond]
    _ ≤ _ := add_le_add (le_refl _) (operator_mul_hs _ _)

/-- Matrix-valued recurrence behind (9.4), leaving the CFC covariance and
one-step remainder bounds as explicit inputs rather than hidden assumptions. -/
theorem weighted_translation_accumulation {d : ℕ} (s : State d) (V : Mat d)
    (hV : Domain.unitary.Holds V) (δ B C : ℝ) (hδ : 0≤δ)
    (error remainder : ℕ → Mat d) (h0 : error 0=0)
    (hstep : ∀ i,error (i+1)=V.conjTranspose*error i*V+remainder i)
    (hnorm : ∀ i,‖error i‖≤B) (hrem : ∀ i,weighted s (remainder i)≤C*δ)
    (hstate : hs (comm V s.xi)≤δ) :
    ∀ i : ℕ, weighted s (error i) ≤ (i:ℝ) * (B+C) * δ := by
  apply linear_accumulation (fun i => weighted s (error i)) (B+C) δ
  · simp only [h0,weighted,Matrix.zero_mul,hs,hsNorm,hsSquared,Matrix.zero_apply,
      Complex.normSq_zero,Finset.sum_const_zero,Real.sqrt_zero]
  · intro i
    rw [hstep]
    calc
      _ ≤ weighted s (V.conjTranspose*error i*V)+weighted s (remainder i) := weighted_add _ _ _
      _ ≤ (weighted s (error i)+‖error i‖*hs (comm V s.xi))+C*δ :=
        add_le_add (unitary_weighted_transport s V _ hV) (hrem i)
      _ ≤ (weighted s (error i)+B*δ)+C*δ := by
        have hm := mul_le_mul hstate (hnorm i) (norm_nonneg (error i)) hδ
        nlinarith
      _ = _ := by ring

end
end E2
