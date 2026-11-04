import E2.CarryEstimates

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem spectral_repair_carry_step {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (V H : Mat d) (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c)
    (hV : Domain.unitary.Holds V) (hσV : hs (comm V s.xi)≤δ)
    (hstep : weighted s (V.conjTranspose*c.A*V-(c.A-1+(7/4:ℂ) • H))≤δ)
    (r : SpectralRepair c s δ K)
    (hcarry : weighted s (H-matrixFunction carryFunction r.Ahat)≤32*K*δ) :
    weighted s (V.conjTranspose*r.Ahat*V-matrixFunction (cantorTranslation 1) r.Ahat)≤64*K*δ := by
  have hKd : δ≤K*δ := by nlinarith
  have hclose : weighted s (r.Ahat-c.A)≤K*δ :=
    le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hn : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans (by
    linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hc.1.1])
  have ht := unitary_weighted_transport s V (r.Ahat-c.A) hV
  have htrans : weighted s (V.conjTranspose*(r.Ahat-c.A)*V)≤K*δ+2*δ := by
    have hm := mul_le_mul hn hσV (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith
  have he : V.conjTranspose*r.Ahat*V-matrixFunction (cantorTranslation 1) r.Ahat=
      V.conjTranspose*(r.Ahat-c.A)*V+(V.conjTranspose*c.A*V-(c.A-1+(7/4:ℂ) • H))+
      (c.A-r.Ahat)+(7/4:ℂ) • (H-matrixFunction carryFunction r.Ahat) := by
    rw [matrix_function_carry_step r.spectrum]
    simp only [Matrix.mul_sub,Matrix.sub_mul,smul_sub]
    module
  rw [he]
  calc
    _ ≤ weighted s (V.conjTranspose*(r.Ahat-c.A)*V)+
        weighted s (V.conjTranspose*c.A*V-(c.A-1+(7/4:ℂ) • H))+
        weighted s (c.A-r.Ahat)+weighted s ((7/4:ℂ) • (H-matrixFunction carryFunction r.Ahat)) :=
      (weighted_add _ _ _).trans (add_le_add
        ((weighted_add _ _ _).trans (add_le_add (weighted_add _ _ _) le_rfl)) le_rfl)
    _ ≤ (K*δ+2*δ)+δ+K*δ+(7/4)*(32*K*δ) := by
      have hr := weighted_real_smul s (7/4) (H-matrixFunction carryFunction r.Ahat) (by norm_num)
      norm_num at hr
      rw [hr,weighted_sub_symm s c.A r.Ahat]
      gcongr
    _ ≤ _ := by linarith

/-- Uniform Lipschitz control applies to each new one-step remainder. -/
theorem cantor_translation_linear {d : ℕ} (s : State d) (δ K : ℝ) (A V : Mat d)
    (hδ : 0≤δ) (hK : 1≤K) (hA : HasCantorSpectrum A)
    (hV : Domain.unitary.Holds V) (hσV : hs (comm V s.xi)≤δ)
    (hσA : hs (comm A s.xi)≤K*δ)
    (hstep : weighted s (V.conjTranspose*A*V-matrixFunction (cantorTranslation 1) A)≤64*K*δ) :
    ∀ i : ℕ,weighted s (translate V.conjTranspose A i-matrixFunction (cantorTranslation i) A)≤
      (i:ℝ)*(138*K)*δ := by
  let error := fun i => translate V.conjTranspose A i-matrixFunction (cantorTranslation i) A
  let remainder := fun i => matrixFunction (cantorTranslation i) (V.conjTranspose*A*V)-
    matrixFunction (cantorTranslation i) (matrixFunction (cantorTranslation 1) A)
  have h0 : error 0=0 := by
    have hf : matrixFunction (cantorTranslation 0) A=A := by
      calc
        _ = matrixFunction id A := matrix_function_congr hA.1 _ _ (fun x hx => cantor_translation_zero (hA.2 hx))
        _ = _ := matrix_function_id hA.1
    simp only [error,translate,pow_zero,Matrix.one_mul,Matrix.mul_one,hf,sub_self]
  have hn : ∀ i,‖error i‖≤2 := by
    intro i
    exact (norm_sub_le _ _).trans (by
      have ht := translate_norm s V.conjTranspose A (unitary_adjoint hV) i
      have hg := cantor_function_norm hA (cantorTranslation i)
        (fun _ hx => cantor_mem_bounds (cantor_translation_mem i hx))
      linarith [cantor_matrix_norm hA])
  have hσg : hs (comm (matrixFunction (cantorTranslation 1) A) s.xi)≤2*K*δ := by
    have hh := state_functional_calculus s A (cantorTranslation 1) 2 hA.1
      (cantorTranslation_lipschitz 1).lipschitzOnWith
    norm_num at hh
    linarith
  have hr : ∀ i,weighted s (remainder i)≤(136*K)*δ := by
    intro i
    have hh := weighted_functional_calculus s (V.conjTranspose*A*V)
      (matrixFunction (cantorTranslation 1) A) (cantorTranslation i) 2
      (by simpa only [Matrix.conjTranspose_conjTranspose] using unitary_conjugate_hermitian V.conjTranspose A hA.1)
      (matrix_function_hermitian hA.1 _) (cantorTranslation_lipschitz i).lipschitzOnWith
    norm_num at hh
    dsimp [remainder]
    linarith
  have he : ∀ i,error (i+1)=V.conjTranspose*error i*V+remainder i := by
    intro i
    have hcov := matrix_function_conjugate V.conjTranspose A (unitary_adjoint hV) hA.1 (cantorTranslation i)
    simp only [Matrix.conjTranspose_conjTranspose] at hcov
    have hcomp := matrix_function_translate_comp hA i 1
    dsimp [error,remainder]
    rw [translate_succ]
    simp only [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,hcov,hcomp]
    abel
  have hb := weighted_translation_accumulation s V hV δ 2 (136*K) hδ error remainder h0 he hn hr hσV
  intro i
  calc
    _ ≤ (i:ℝ)*(2+136*K)*δ := hb i
    _ ≤ _ := by gcongr; linarith

end
end E2
