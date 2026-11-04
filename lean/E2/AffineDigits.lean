import E2.AffineRounding

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

theorem repaired_affine_tail {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (Ahat : Mat d) (hδ : 0≤δ) (hA : Domain.positiveContraction.Holds c.A)
    (hT : Domain.unitary.Holds c.T) (hK : HasCantorSpectrum Ahat)
    (hσT : hs (comm c.T s.xi)≤δ)
    (hAff : weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))≤δ)
    (hclose : weighted s (Ahat-c.A)≤150*δ)
    (hbase : weighted s (c.P-matrixFunction digitFunction Ahat)≤414*δ) :
    weighted s (c.T*Ahat*c.T.conjTranspose-matrixFunction tailFunction Ahat)≤2000*δ := by
  have hn : ‖Ahat-c.A‖≤2 := (norm_sub_le _ _).trans (by linarith [cantor_matrix_norm hK,positive_contraction_norm hA])
  have ht := unitary_weighted_transport s c.T.conjTranspose (Ahat-c.A) (unitary_adjoint hT)
  simp only [Matrix.conjTranspose_conjTranspose,unitary_adjoint_state_commutator s c.T hT] at ht
  have hm := mul_le_mul hn hσT (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hmove : weighted s (c.T*(Ahat-c.A)*c.T.conjTranspose)≤152*δ := by nlinarith
  have he : c.T*Ahat*c.T.conjTranspose-matrixFunction tailFunction Ahat=
      c.T*(Ahat-c.A)*c.T.conjTranspose+
      (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))+
      (4:ℂ) • (c.A-Ahat)-(3:ℂ) • (c.P-matrixFunction digitFunction Ahat) := by
    rw [matrix_function_tail hK.1]
    simp only [Matrix.mul_sub,Matrix.sub_mul,smul_sub]
    module
  rw [he]
  have h := (weighted_sub_le s
      (c.T*(Ahat-c.A)*c.T.conjTranspose+
        (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))+(4:ℂ) • (c.A-Ahat))
      ((3:ℂ) • (c.P-matrixFunction digitFunction Ahat))).trans
    (add_le_add ((weighted_add _ _ _).trans (add_le_add (weighted_add _ _ _) le_rfl)) le_rfl)
  simp only [weighted_smul,weighted_sub_symm s c.A Ahat] at h
  norm_num at h
  nlinarith

theorem matrix_function_digit_tail {d : ℕ} (A : Mat d) (hA : A.IsHermitian) (j : ℕ) :
    matrixFunction (digitAt j) (matrixFunction tailFunction A)=matrixFunction (digitAt (j+1)) A := by
  rw [matrix_function_comp hA]
  congr 1

theorem spectral_digit_conjugation_error {d : ℕ} (s : State d) (δ : ℝ) (A T : Mat d)
    (hδ : 0≤δ) (hA : HasCantorSpectrum A) (hT : Domain.unitary.Holds T)
    (hσA : hs (comm A s.xi)≤301*δ)
    (htail : weighted s (T*A*T.conjTranspose-matrixFunction tailFunction A)≤2000*δ) (j : ℕ) :
    weighted s (T*matrixFunction (digitAt j) A*T.conjTranspose-matrixFunction (digitAt (j+1)) A)≤8816*4^j*δ := by
  have hσS : hs (comm (matrixFunction tailFunction A) s.xi)≤1204*δ := by
    have h := state_functional_calculus s A tailFunction 4 hA.1 tailFunction_lipschitz.lipschitzOnWith
    norm_num at h
    linarith
  rw [matrix_function_conjugate T A hT hA.1,←matrix_function_digit_tail A hA.1 j]
  have h := weighted_functional_calculus s (T*A*T.conjTranspose) (matrixFunction tailFunction A)
    (digitAt j) (2*4^j) (unitary_conjugate_hermitian T A hA.1)
    (matrix_function_hermitian hA.1 _) (digitAt_lipschitz j).lipschitzOnWith
  norm_num only [NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_pow] at h
  calc
    _≤(2*4^j)*(2000*δ+2*(1204*δ)) := h.trans (by gcongr)
    _=_ := by ring

theorem spectral_digit_telescope {d : ℕ} (s : State d) (δ : ℝ) (A T : Mat d)
    (hδ : 0≤δ) (hA : HasCantorSpectrum A) (hT : Domain.unitary.Holds T)
    (hσT : hs (comm T s.xi)≤δ)
    (hstep : ∀ j, weighted s (T*matrixFunction (digitAt j) A*T.conjTranspose-
      matrixFunction (digitAt (j+1)) A)≤8816*4^j*δ) :
    ∀ j, weighted s (translate T (matrixFunction digitFunction A) j-
      matrixFunction (digitAt j) A)≤10000*4^j*δ := by
  let E := fun j => translate T (matrixFunction digitFunction A) j-matrixFunction (digitAt j) A
  let R := fun j => T*matrixFunction (digitAt j) A*T.conjTranspose-matrixFunction (digitAt (j+1)) A
  have hnP : ‖matrixFunction digitFunction A‖≤1 :=
    cantor_function_norm hA _ (fun x hx => by simpa [digitAt] using cantor_digit_bounds 0 hx)
  have hn (j : ℕ) : ‖E j‖≤2 := by
    have ht := translate_norm s T (matrixFunction digitFunction A) hT j
    have hf := cantor_function_norm hA (digitAt j) (fun x hx => cantor_digit_bounds j hx)
    exact (norm_sub_le _ _).trans (by linarith)
  have h0 : E 0=0 := by simp [E,translate,digitAt]
  have he (j : ℕ) : E (j+1)=T*E j*T.conjTranspose+R j := by
    dsimp [E,R]
    rw [translate_succ]
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    abel
  have hbound : ∀ j, weighted s (E j)≤10000*4^j*δ := by
    intro j
    induction j with
    | zero => rw [h0]; simp only [weighted,Matrix.zero_mul,hs_matrix_zero]; positivity
    | succ j ih =>
      have ht := unitary_weighted_transport s T.conjTranspose (E j) (unitary_adjoint hT)
      simp only [Matrix.conjTranspose_conjTranspose,unitary_adjoint_state_commutator s T hT] at ht
      have hm := mul_le_mul (hn j) hσT (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
      have hr : weighted s (R j)≤8816*4^j*δ := hstep j
      have hp : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
      have hpδ := mul_le_mul_of_nonneg_right hp hδ
      rw [he]
      have ha := weighted_add s (T*E j*T.conjTranspose) (R j)
      rw [pow_succ]
      nlinarith only [ih,ht,hm,hr,hpδ,ha,hδ]
  exact hbound

theorem raw_digit_from_repair {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d) (A : Mat d)
    (hδ : 0≤δ) (hA : HasCantorSpectrum A) (hP : Domain.projection.Holds c.P)
    (hT : Domain.unitary.Holds c.T) (hσT : hs (comm c.T s.xi)≤δ)
    (hbase : weighted s (c.P-matrixFunction digitFunction A)≤414*δ)
    (hstep : ∀ j, weighted s (c.T*matrixFunction (digitAt j) A*c.T.conjTranspose-
      matrixFunction (digitAt (j+1)) A)≤8816*4^j*δ) :
    ∀ j, weighted s (rawDigit c j-matrixFunction (digitAt j) A)≤11000*4^j*δ := by
  have hnP := projection_norm_le hP
  have hnp : ‖matrixFunction digitFunction A‖≤1 :=
    cantor_function_norm hA _ (fun x hx => by simpa [digitAt] using cantor_digit_bounds 0 hx)
  have hn : ‖c.P-matrixFunction digitFunction A‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have htelescope := spectral_digit_telescope s δ A c.T hδ hA hT hσT hstep
  have hjpow : ∀ j : ℕ, (j:ℝ)≤(4:ℝ)^j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hp : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
      push_cast
      rw [pow_succ]
      linarith
  intro j
  have ht := translate_weighted s c.T (c.P-matrixFunction digitFunction A) hT δ hδ hσT j
  have hmove : weighted s (translate c.T (c.P-matrixFunction digitFunction A) j)≤414*δ+2*(j*δ) := by
    have hm := mul_le_mul_of_nonneg_right hn (mul_nonneg (Nat.cast_nonneg j) hδ)
    nlinarith only [ht,hm,hbase]
  have he : rawDigit c j-matrixFunction (digitAt j) A=
      translate c.T (c.P-matrixFunction digitFunction A) j+
        (translate c.T (matrixFunction digitFunction A) j-matrixFunction (digitAt j) A) := by
    rw [translate_sub]
    change translate c.T c.P j-matrixFunction (digitAt j) A=_
    abel
  rw [he]
  have ha := weighted_add s (translate c.T (c.P-matrixFunction digitFunction A) j)
    (translate c.T (matrixFunction digitFunction A) j-matrixFunction (digitAt j) A)
  have h1 : δ≤4^j*δ := by
    simpa using mul_le_mul_of_nonneg_right (show (1:ℝ)≤4^j from one_le_pow₀ (by norm_num)) hδ
  have hj := mul_le_mul_of_nonneg_right (hjpow j) hδ
  have herr := htelescope j
  nlinarith only [ha,hmove,h1,hj,herr,hδ]

end
end E2

#print axioms E2.repaired_affine_tail
#print axioms E2.matrix_function_digit_tail
#print axioms E2.spectral_digit_conjugation_error
#print axioms E2.spectral_digit_telescope
#print axioms E2.raw_digit_from_repair
