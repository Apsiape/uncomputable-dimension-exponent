import E2.CarryTranslations
import E2.CarryRoutingTools

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem address_digit_translation {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (V : Mat d) (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c)
    (hV : Domain.unitary.Holds V) (hσV : hs (comm V s.xi)≤δ)
    (r : SpectralRepair c s δ K)
    (htrans : ∀ i,weighted s (translate V.conjTranspose r.Ahat i-matrixFunction (cantorTranslation i) r.Ahat)≤
      (i:ℝ)*(138*K)*δ) (i j : ℕ) :
    weighted s (translate V.conjTranspose (rawDigit c j) i-
      matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat))≤600*K*(i+1)*4^j*δ := by
  have hK0 : 0≤K := by linarith
  have hq : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
  have hnraw : ‖rawDigit c j‖≤1 :=
    projection_norm_le (translate_projection c.T c.P hc.1.2.2.1 hc.1.2.1 j)
  have hnf : ‖matrixFunction (digitAt j) r.Ahat‖≤1 :=
    cantor_function_norm r.spectrum _ (fun _ hx => cantor_digit_bounds j hx)
  have hne : ‖rawDigit c j-matrixFunction (digitAt j) r.Ahat‖≤2 :=
    (norm_sub_le _ _).trans (by linarith)
  have hσadj : hs (comm V.conjTranspose s.xi)≤δ := by
    rwa [unitary_adjoint_state_commutator s V hV]
  have ht := translate_weighted s V.conjTranspose
    (rawDigit c j-matrixFunction (digitAt j) r.Ahat) (unitary_adjoint hV) δ hδ hσadj i
  have ht' : weighted s (translate V.conjTranspose
      (rawDigit c j-matrixFunction (digitAt j) r.Ahat) i)≤K*4^j*δ+2*(i*δ) := by
    have hm := mul_le_mul_of_nonneg_right hne (mul_nonneg (Nat.cast_nonneg i) hδ)
    linarith [r.digits j]
  have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hσg : hs (comm (matrixFunction (cantorTranslation i) r.Ahat) s.xi)≤2*K*δ := by
    have hh := state_functional_calculus s r.Ahat (cantorTranslation i) 2 r.spectrum.1
      (cantorTranslation_lipschitz i).lipschitzOnWith
    norm_num at hh
    linarith
  have hf := weighted_functional_calculus s (translate V.conjTranspose r.Ahat i)
    (matrixFunction (cantorTranslation i) r.Ahat) (digitAt j) (2*4^j)
    (translate_hermitian _ _ r.spectrum.1 i) (matrix_function_hermitian r.spectrum.1 _)
    (digitAt_lipschitz j).lipschitzOnWith
  simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat] at hf
  have hf' : weighted s (translate V.conjTranspose (matrixFunction (digitAt j) r.Ahat) i-
      matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat))≤
      (2*4^j)*((i:ℝ)*(138*K)*δ+4*K*δ) := by
    rw [translate_matrix_function _ _ (unitary_adjoint hV) r.spectrum.1]
    nlinarith only [hf,htrans i,hσg,show (0:ℝ)≤4^j by positivity]
  have he : translate V.conjTranspose (rawDigit c j) i-
      matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat)=
      translate V.conjTranspose (rawDigit c j-matrixFunction (digitAt j) r.Ahat) i+
      (translate V.conjTranspose (matrixFunction (digitAt j) r.Ahat) i-
      matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat)) := by
    rw [translate_sub]; abel
  rw [he]
  calc
    _ ≤ weighted s (translate V.conjTranspose (rawDigit c j-matrixFunction (digitAt j) r.Ahat) i)+
      weighted s (translate V.conjTranspose (matrixFunction (digitAt j) r.Ahat) i-
        matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat)) := weighted_add _ _ _
    _ ≤ K*4^j*δ+2*(i*δ)+(2*4^j)*((i:ℝ)*(138*K)*δ+4*K*δ) := add_le_add ht' hf'
    _ ≤ _ := by
      have hi : (i:ℝ)*δ≤K*(i:ℝ)*4^j*δ := by
        calc
          _ = 1*(i:ℝ)*1*δ := by ring
          _ ≤ _ := by gcongr
      have hmain : 0≤K*((i:ℝ)+1)*4^j*δ := by positivity
      nlinarith [mul_nonneg (mul_nonneg hK0 hδ) (Nat.cast_nonneg i)]

theorem spectral_repair_address_routing {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (V : Mat d) (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c)
    (hV : Domain.unitary.Holds V) (hσV : hs (comm V s.xi)≤δ)
    (r : SpectralRepair c s δ K)
    (htrans : ∀ i,weighted s (translate V.conjTranspose r.Ahat i-matrixFunction (cantorTranslation i) r.Ahat)≤
      (i:ℝ)*(138*K)*δ) (i j : ℕ) (J : Mat d) (hnJ : ‖J‖≤1)
    (hJA : weighted s (comm J c.A)≤δ) (hσJ : hs (comm J s.xi)≤δ) :
    weighted s (comm (translate V J i) (rawDigit c j))≤2048*K*(i+1)*4^j*δ := by
  let B := translate V.conjTranspose (rawDigit c j) i
  let F := matrixFunction (digitAt j) (matrixFunction (cantorTranslation i) r.Ahat)
  have hK0 : 0≤K := by linarith
  have hi0 : (0:ℝ)≤(i:ℝ) := Nat.cast_nonneg i
  have hq : (1:ℝ)≤4^j := one_le_pow₀ (by norm_num)
  have hσA : hs (comm r.Ahat s.xi)≤K*δ :=
    le_trans (le_add_of_nonneg_left (weighted_nonneg s _)) r.closeness
  have hnB : ‖B‖≤1 := projection_norm_le
    (translate_projection _ _ (unitary_adjoint hV)
      (translate_projection c.T c.P hc.1.2.2.1 hc.1.2.1 j) i)
  have hnF : ‖F‖≤1 := by
    dsimp [F]
    rw [matrix_function_comp r.spectrum.1]
    exact cantor_function_norm r.spectrum _ (fun _ hx => cantor_digit_bounds j (cantor_translation_mem i hx))
  have hnD : ‖B-F‖≤2 := (norm_sub_le _ _).trans (by linarith)
  have hD : weighted s (B-F)≤600*K*(i+1)*4^j*δ :=
    address_digit_translation s δ K c V hδ hK hc hV hσV r htrans i j
  have hJhat := repaired_address_commutator s δ K c hδ hK hc r J hnJ hJA hσJ
  have hJF : weighted s (comm J F)≤28*K*4^j*δ := by
    have hf := commutator_functional_calculus s r.Ahat J
      (fun x => digitAt j (cantorTranslation i x)) ((2*4^j)*2) r.spectrum.1 hnJ
      ((digitAt_lipschitz j).comp (cantorTranslation_lipschitz i)).lipschitzOnWith
    simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat] at hf
    dsimp [F]
    rw [matrix_function_comp r.spectrum.1]
    nlinarith only [hf,hJhat,hσA,show (0:ℝ)≤4^j by positivity]
  have hJD := commutator_replace s (B-F) J hnJ
  rw [weighted_comm_symm] at hJD
  have hm := mul_le_mul hnD hσJ (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hJB : weighted s (comm J B)≤1300*K*(i+1)*4^j*δ := by
    have he : B=F+(B-F) := by abel
    have htriangle : weighted s (comm J B)≤weighted s (comm J F)+weighted s (comm J (B-F)) := by
      conv_lhs => rw [he,comm_add_right]
      exact weighted_add _ _ _
    have hd : δ≤K*(i+1)*4^j*δ := by
      calc
        _ = 1*1*1*δ := by ring
        _ ≤ _ := by
          have hi1 : (1:ℝ)≤(i:ℝ)+1 := by linarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul hK hi1 zero_le_one hK0) hq zero_le_one (by positivity)) hδ
    have hbase : K*4^j*δ≤K*(i+1)*4^j*δ := by
      gcongr <;> first | positivity | nlinarith [mul_nonneg hK0 hi0]
    nlinarith
  have ht := translate_weighted s V (comm J B) hV δ hδ hσV i
  have hncomm := norm_comm_contractions J B hnJ hnB
  have hcost := mul_le_mul_of_nonneg_right hncomm (mul_nonneg (Nat.cast_nonneg i) hδ)
  have he : translate V (comm J B) i=comm (translate V J i) (rawDigit c j) := by
    rw [translate_comm _ _ _ hV]
    dsimp [B]
    rw [translate_inverse _ _ hV]
  rw [he] at ht
  have hi : (i:ℝ)*δ≤K*(i+1)*4^j*δ := by
    calc
      _ = 1*(i:ℝ)*1*δ := by ring
      _ ≤ _ := by
        gcongr <;> first | positivity | nlinarith [mul_nonneg hK0 hi0,mul_nonneg (sub_nonneg.mpr hK) hi0]
  nlinarith

end
end E2
