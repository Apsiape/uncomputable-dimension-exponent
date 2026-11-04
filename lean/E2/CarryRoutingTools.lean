import E2.CarryTools

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem unitary_conjugation_mul {d : ℕ} (V A B : Mat d) (hV : Domain.unitary.Holds V) :
    (V*A*V.conjTranspose)*(V*B*V.conjTranspose)=V*(A*B)*V.conjTranspose := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V.conjTranspose V,hV.1,Matrix.one_mul]

theorem unitary_conjugation_inverse {d : ℕ} (V A : Mat d) (hV : Domain.unitary.Holds V) :
    V*(V.conjTranspose*A*V)*V.conjTranspose=A := by
  calc
    _ = (V*V.conjTranspose)*A*(V*V.conjTranspose) := by noncomm_ring
    _ = _ := by rw [hV.2]; simp only [Matrix.one_mul,Matrix.mul_one]

theorem unitary_conjugation_projection {d : ℕ} (V P : Mat d) (hV : Domain.unitary.Holds V)
    (hP : Domain.projection.Holds P) : Domain.projection.Holds (V*P*V.conjTranspose) := by
  constructor
  · simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hP.1,Matrix.mul_assoc]
  · rw [unitary_conjugation_mul _ _ _ hV,hP.2]

theorem translate_projection {d : ℕ} (V P : Mat d) (hV : Domain.unitary.Holds V)
    (hP : Domain.projection.Holds P) (i : ℕ) : Domain.projection.Holds (translate V P i) := by
  rw [translate_eq_conjugate]
  exact unitary_conjugation_projection _ _ (unitary_power hV i) hP

theorem translate_sub {d : ℕ} (V A B : Mat d) (i : ℕ) :
    translate V (A-B) i=translate V A i-translate V B i := by
  simp only [translate,Matrix.mul_sub,Matrix.sub_mul]

theorem translate_comm {d : ℕ} (V A B : Mat d) (hV : Domain.unitary.Holds V) (i : ℕ) :
    translate V (comm A B) i=comm (translate V A i) (translate V B i) := by
  simp only [translate_eq_conjugate,comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,
    unitary_conjugation_mul _ _ _ (unitary_power hV i)]

theorem translate_inverse {d : ℕ} (V A : Mat d) (hV : Domain.unitary.Holds V) (i : ℕ) :
    translate V (translate V.conjTranspose A i) i=A := by
  simp only [translate_eq_conjugate,← Matrix.conjTranspose_pow,Matrix.conjTranspose_conjTranspose]
  exact unitary_conjugation_inverse _ _ (unitary_power hV i)

theorem translate_matrix_function {d : ℕ} (V A : Mat d) (hV : Domain.unitary.Holds V)
    (hA : A.IsHermitian) (f : ℝ → ℝ) (i : ℕ) :
    translate V (matrixFunction f A) i=matrixFunction f (translate V A i) := by
  simp only [translate_eq_conjugate]
  exact matrix_function_conjugate _ _ (unitary_power hV i) hA f

theorem translate_hermitian {d : ℕ} (V A : Mat d) (hA : A.IsHermitian) (i : ℕ) :
    (translate V A i).IsHermitian := by
  rw [translate_eq_conjugate]
  exact unitary_conjugate_hermitian _ _ hA

theorem weighted_comm_symm {d : ℕ} (s : State d) (A B : Mat d) :
    weighted s (comm A B)=weighted s (comm B A) := by
  exact weighted_sub_symm s (A*B) (B*A)

theorem comm_add_right {d : ℕ} (A B C : Mat d) : comm A (B+C)=comm A B+comm A C := by
  simp only [comm,Companion.Analytic.comm,Matrix.mul_add,Matrix.add_mul]
  abel

theorem repaired_address_commutator {d : ℕ} (s : State d) (δ K : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hK : 1≤K) (hc : ClockApprox s δ c) (r : SpectralRepair c s δ K)
    (J : Mat d) (hnJ : ‖J‖≤1) (hJA : weighted s (comm J c.A)≤δ)
    (hσJ : hs (comm J s.xi)≤δ) : weighted s (comm J r.Ahat)≤5*K*δ := by
  have hclose : weighted s (r.Ahat-c.A)≤K*δ :=
    le_trans (le_add_of_nonneg_right (hsNorm_nonneg _)) r.closeness
  have hn : ‖r.Ahat-c.A‖≤2 := (norm_sub_le _ _).trans (by
    linarith [cantor_matrix_norm r.spectrum,positive_contraction_norm hc.1.1])
  have hh := commutator_replace s (r.Ahat-c.A) J hnJ
  rw [weighted_comm_symm] at hh
  have hm := mul_le_mul hn hσJ (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have he : r.Ahat=c.A+(r.Ahat-c.A) := by abel
  calc
    _ = weighted s (comm J c.A+comm J (r.Ahat-c.A)) := by conv_lhs => rw [he,comm_add_right]
    _ ≤ weighted s (comm J c.A)+weighted s (comm J (r.Ahat-c.A)) := weighted_add _ _ _
    _ ≤ _ := by nlinarith

end
end E2
