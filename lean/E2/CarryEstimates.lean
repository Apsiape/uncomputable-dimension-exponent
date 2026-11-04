import E2.CarryTools

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic
set_option maxHeartbeats 300000

theorem spectral_repair_affine {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K) :
    weighted s (c.T*r.Ahat*c.T.conjTranspose-matrixFunction tailFunction r.Ahat)≤11*K*δ := by
  have hKd : δ≤K*δ := by nlinarith
  have hclose : weighted s (r.Ahat-c.A)≤K*δ :=
    le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hA : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans (by
    linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hc.1.1])
  have hp : weighted s (c.P-matrixFunction digitFunction r.Ahat)≤K*δ := by
    simpa only [rawDigit,translate,pow_zero,Matrix.one_mul,Matrix.mul_one,digitAt_zero,mul_one] using r.digits 0
  have hT := hc.2.2 c.T (by simp [ClockData.variables])
  have ht := unitary_weighted_transport s c.T.conjTranspose (r.Ahat-c.A) (unitary_adjoint hc.1.2.2.1)
  simp only [Matrix.conjTranspose_conjTranspose,
    unitary_adjoint_state_commutator s c.T hc.1.2.2.1] at ht
  have ht' : weighted s (c.T*(r.Ahat-c.A)*c.T.conjTranspose)≤K*δ+2*δ := by
    have hm := mul_le_mul hA hT (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith
  have hf := hc.2.1 (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))
    (by simp [ClockData.defects])
  have he : c.T*r.Ahat*c.T.conjTranspose-matrixFunction tailFunction r.Ahat=
      c.T*(r.Ahat-c.A)*c.T.conjTranspose+
      (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))+
      (4:ℂ) • (c.A-r.Ahat)-(3:ℂ) • (c.P-matrixFunction digitFunction r.Ahat) := by
    rw [matrix_function_tail r.spectrum.1]
    simp only [Matrix.mul_sub,Matrix.sub_mul,smul_sub]
    module
  rw [he]
  calc
    _ ≤ (weighted s (c.T*(r.Ahat-c.A)*c.T.conjTranspose)+
      weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P)))+
      weighted s ((4:ℂ) • (c.A-r.Ahat))+weighted s ((3:ℂ) • (c.P-matrixFunction digitFunction r.Ahat)) :=
      (weighted_sub_le _ _ _).trans (add_le_add (weighted_add _ _ _) le_rfl) |>.trans
        (add_le_add (add_le_add (weighted_add _ _ _) le_rfl) le_rfl)
    _ ≤ (K*δ+2*δ+δ)+4*(K*δ)+3*(K*δ) := by
      simp only [weighted_smul,weighted_sub_symm s c.A r.Ahat]
      norm_num
      gcongr
    _ ≤ _ := by nlinarith

theorem spectral_repair_carry_tail {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K) :
    weighted s (c.T*matrixFunction carryFunction r.Ahat*c.T.conjTranspose-
      matrixFunction carryFunction (matrixFunction tailFunction r.Ahat))≤38*K*δ := by
  have hσ : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hS := state_functional_calculus s r.Ahat tailFunction 4 r.spectrum.1
    tailFunction_lipschitz.lipschitzOnWith
  norm_num at hS
  have hσS : hs (comm (matrixFunction tailFunction r.Ahat) s.xi)≤4*K*δ := by
    calc
      _ ≤ 4*hs (comm r.Ahat s.xi) := hS
      _ ≤ _ := by nlinarith
  rw [matrix_function_conjugate c.T r.Ahat hc.1.2.2.1 r.spectrum.1]
  have hf := weighted_functional_calculus s (c.T*r.Ahat*c.T.conjTranspose)
    (matrixFunction tailFunction r.Ahat) carryFunction 2
    (unitary_conjugate_hermitian _ _ r.spectrum.1)
    (matrix_function_hermitian r.spectrum.1 _) carryFunction_lipschitz.lipschitzOnWith
  have ha := spectral_repair_affine s δ K c hδ hK hc r
  norm_num at hf
  linarith

/-- Absorbs the quarter-sized recursive carry error on the original state. -/
theorem spectral_repair_carry {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (H : Mat d) (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c)
    (hH : Domain.positiveContraction.Holds H)
    (hrec : weighted s (H-((1-c.P)+(1/4:ℂ) • (c.P*c.T*H*c.T.conjTranspose)))≤δ)
    (r : SpectralRepair c s δ K) :
    weighted s (H-matrixFunction carryFunction r.Ahat)≤32*K*δ := by
  let W := matrixFunction carryFunction r.Ahat
  let p := matrixFunction digitFunction r.Ahat
  let S := matrixFunction tailFunction r.Ahat
  let Z := matrixFunction carryFunction S
  let E := H-W
  have hKd : δ≤K*δ := by nlinarith
  have hσ : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hnW : ‖W‖≤1 := cantor_function_norm r.spectrum _ (fun _ hx => cantor_carry_bounds hx)
  have hnE : ‖E‖≤2 := (norm_sub_le _ _).trans (by linarith [positive_contraction_norm hH])
  have hnP : ‖c.P‖≤1 := projection_norm_le hc.1.2.1
  have hnp : ‖p‖≤1 := cantor_function_norm r.spectrum _ (fun _ hx => by
    simpa only [digitAt,Function.iterate_zero,Function.id_def] using cantor_digit_bounds 0 hx)
  have hnD : ‖c.P-p‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have hp : weighted s (c.P-p)≤K*δ := by
    simpa only [rawDigit,translate,pow_zero,Matrix.one_mul,Matrix.mul_one,digitAt_zero,mul_one] using r.digits 0
  have hspecS : HasCantorSpectrum S := ⟨matrix_function_hermitian r.spectrum.1 _,by
    rw [matrix_function_spectrum r.spectrum.1]
    rintro _ ⟨x,hx,rfl⟩
    exact cantor_tail_mem (r.spectrum.2 hx)⟩
  have hnZ : ‖Z‖≤1 := cantor_function_norm hspecS _ (fun _ hx => cantor_carry_bounds hx)
  have hσS : hs (comm S s.xi)≤4*K*δ := by
    have hh := state_functional_calculus s r.Ahat tailFunction 4 r.spectrum.1
      tailFunction_lipschitz.lipschitzOnWith
    norm_num at hh
    change hs (comm S s.xi)≤4*hs (comm r.Ahat s.xi) at hh
    linarith
  have hσZ : hs (comm Z s.xi)≤8*K*δ := by
    have hh := state_functional_calculus s S carryFunction 2 hspecS.1
      carryFunction_lipschitz.lipschitzOnWith
    norm_num at hh
    change hs (comm Z s.xi)≤2*hs (comm S s.xi) at hh
    linarith
  have hright : weighted s ((c.P-p)*Z)≤17*K*δ := by
    calc
      _ ≤ ‖Z‖*weighted s (c.P-p)+‖c.P-p‖*hs (comm Z s.xi) := weighted_right _ _ _
      _ ≤ 1*(K*δ)+2*(8*K*δ) := add_le_add
        (mul_le_mul hnZ hp (weighted_nonneg _ _) (by norm_num))
        (mul_le_mul hnD hσZ (hsNorm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hT := hc.2.2 c.T (by simp [ClockData.variables])
  have ht := unitary_weighted_transport s c.T.conjTranspose E (unitary_adjoint hc.1.2.2.1)
  simp only [Matrix.conjTranspose_conjTranspose,
    unitary_adjoint_state_commutator s c.T hc.1.2.2.1] at ht
  have htrans : weighted s (c.T*E*c.T.conjTranspose)≤weighted s E+2*δ := by
    have hm := mul_le_mul hnE hT (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith
  have hrecpart : weighted s (c.P*(c.T*E*c.T.conjTranspose))≤weighted s E+2*δ := by
    calc
      _ ≤ ‖c.P‖*weighted s (c.T*E*c.T.conjTranspose) := weighted_left _ _ _
      _ ≤ 1*(weighted s E+2*δ) := mul_le_mul hnP htrans (weighted_nonneg _ _) (by norm_num)
      _ = _ := one_mul _
  have htail := spectral_repair_carry_tail s δ K c hδ hK hc r
  have htailpart : weighted s (c.P*(c.T*W*c.T.conjTranspose-Z))≤38*K*δ := by
    calc
      _ ≤ ‖c.P‖*weighted s (c.T*W*c.T.conjTranspose-Z) := weighted_left _ _ _
      _ ≤ 1*(38*K*δ) := mul_le_mul hnP htail (weighted_nonneg _ _) (by norm_num)
      _ = _ := one_mul _
  have he : E=(H-((1-c.P)+(1/4:ℂ) • (c.P*c.T*H*c.T.conjTranspose)))-(c.P-p)+
      (1/4:ℂ) • (c.P*(c.T*E*c.T.conjTranspose))+
      (1/4:ℂ) • (c.P*(c.T*W*c.T.conjTranspose-Z))+
      (1/4:ℂ) • ((c.P-p)*Z) := by
    have hw := matrix_function_carry_recursion r.spectrum
    change W=1-p+(1/4:ℂ) • (p*Z) at hw
    calc
      E = H-(1-p+(1/4:ℂ) • (p*Z)) := by dsimp [E]; rw [← hw]
      _ = _ := by
        dsimp [E]
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc,smul_sub]
        module
  have hbound : weighted s E≤δ+K*δ+(1/4)*(weighted s E+2*δ)+(1/4)*(38*K*δ)+(1/4)*(17*K*δ) := by
    calc
      _ ≤ weighted s (H-((1-c.P)+(1/4:ℂ) • (c.P*c.T*H*c.T.conjTranspose)))+weighted s (c.P-p)+
        weighted s ((1/4:ℂ) • (c.P*(c.T*E*c.T.conjTranspose)))+
        weighted s ((1/4:ℂ) • (c.P*(c.T*W*c.T.conjTranspose-Z)))+
        weighted s ((1/4:ℂ) • ((c.P-p)*Z)) := by
          conv_lhs => rw [he]
          exact (weighted_add _ _ _).trans (add_le_add
            ((weighted_add _ _ _).trans (add_le_add
              ((weighted_add _ _ _).trans (add_le_add (weighted_sub_le _ _ _) le_rfl)) le_rfl)) le_rfl)
      _ ≤ _ := by
        simp only [weighted_smul]
        norm_num
        exact add_le_add (add_le_add (add_le_add (add_le_add hrec hp)
          (mul_le_mul_of_nonneg_left hrecpart (by norm_num)))
          (mul_le_mul_of_nonneg_left htailpart (by norm_num)))
          (mul_le_mul_of_nonneg_left hright (by norm_num))
  change weighted s E≤32*K*δ
  linarith

end
end E2
