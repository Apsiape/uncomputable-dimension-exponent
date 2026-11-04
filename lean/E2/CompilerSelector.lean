import E2.CompilerAnd
import E2.CompilerGadgets

namespace E2.CompilerSelector
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Companion.Analytic

/-- The Pauli compression is a finite polynomial consequence of its square
and anticommutator residuals. This identity needs no hypotheses. -/
theorem pauli_compression_certificate {A : Type*} [Ring A] (X Z : A) :
    (1+X)*Z*(1+X) = (X*Z+Z*X) + (X*Z+Z*X)*X + Z*(1-X*X) := by
  noncomm_ring

theorem pauli_twirl_certificate {A : Type*} [Ring A] (X Z : A) :
    (1+X) + Z*(1+X)*Z - (1+1) =
      (Z*Z-1) + (Z*X+X*Z)*Z - X*(Z*Z-1) := by
  noncomm_ring

theorem pauli_compression {d : ℕ} (X Z : Mat d)
    (hX : X*X=1) (hanti : X*Z+Z*X=0) :
    CompilerBoolean.atom X true * Z * CompilerBoolean.atom X true = 0 := by
  have h := pauli_compression_certificate X Z
  rw [hX, hanti] at h
  simp only [sub_self, mul_zero, zero_mul, add_zero] at h
  simp only [CompilerBoolean.atom, ↓reduceIte, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h, smul_zero]

theorem pauli_twirl {d : ℕ} (X Z : Mat d)
    (hZ : Z*Z=1) (hanti : X*Z+Z*X=0) :
    CompilerBoolean.atom X true + Z*CompilerBoolean.atom X true*Z = 1 := by
  have hanti' : Z*X+X*Z=0 := by simpa [add_comm] using hanti
  have h := pauli_twirl_certificate X Z
  rw [hZ, hanti'] at h
  simp only [sub_self, mul_zero, zero_mul, zero_add, zero_sub, neg_zero] at h
  have he := sub_eq_zero.mp h
  simp only [CompilerBoolean.atom, ↓reduceIte, Matrix.smul_mul, Matrix.mul_smul]
  rw [← smul_add]
  have hs : (1+X) + Z*(1+X)*Z = (1+1 : Mat d) := he
  rw [hs]
  module

/-- The F=SES* substitution. It explicitly retains the source S factor. -/
theorem conjugate_corner {A : Type*} [Ring A] (E S T : A) (hT : T*S=1) :
    E*(S*E*T)*S = E*S*E := by
  calc
    _ = E*S*E*(T*S) := by noncomm_ring
    _ = _ := by rw [hT, mul_one]

/-- Finite selector reconstruction from every translated corner. -/
theorem selector_split {ι : Type*} [Fintype ι] {d : ℕ}
    (Z : ι → Mat d) (E Q p : Mat d) (k : ℂ)
    (hcorner : Q=k • (p*E))
    (hcomm : ∀ i, Z i*p=p*Z i)
    (htwirl : ∑ i, Z i*E*Z i=1) :
    ∑ i, Z i*Q*Z i = k • p := by
  simp_rw [hcorner, Matrix.mul_smul, Matrix.smul_mul]
  rw [← Finset.smul_sum]
  have hterm (i : ι) : Z i*(p*E)*Z i = p*(Z i*E*Z i) := by
    calc
      _ = (Z i*p)*E*Z i := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hcomm i]; simp only [Matrix.mul_assoc]
  simp_rw [hterm]
  rw [← Finset.mul_sum, htwirl, Matrix.mul_one]

/-- Explicit residual certificate for the split, valid before any relation
is imposed. It records both the twirl and source-selector commutator residuals. -/
theorem selector_split_certificate {ι : Type*} [Fintype ι] {d : ℕ}
    (Z : ι → Mat d) (E Q p : Mat d) (k : ℂ) :
    (∑ i, Z i*Q*Z i) - k • p =
      (∑ i, Z i*(Q-k • (p*E))*Z i) +
      k • (∑ i, (Z i*p-p*Z i)*E*Z i) +
      k • (p*((∑ i, Z i*E*Z i)-1)) := by
  have ht (i : ι) : Z i*Q*Z i =
      Z i*(Q-k • (p*E))*Z i +
      k • ((Z i*p-p*Z i)*E*Z i) + k • (p*(Z i*E*Z i)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc, smul_sub]
    module
  conv_lhs => arg 1; arg 2; ext i; rw [ht i]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.mul_sum,
    Matrix.mul_sub, Matrix.mul_one, smul_sub]
  abel

/-- Linear weighted reconstruction. The same state is used on both sides;
the cost for translating a small corner is paid explicitly. -/
theorem selector_weighted_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (s : State d) (Z : ι → Mat d) (Q p : Mat d) (k : ℂ)
    (hidentity : k • p = ∑ i, Z i*Q*Z i)
    (η C B : ℝ) (hη : 0 ≤ η) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hQ : weighted s Q ≤ C*η) (hQn : ‖Q‖ ≤ B)
    (hZ : ∀ i, ‖Z i‖ ≤ 1) (hc : ∀ i, hs (comm (Z i) s.xi) ≤ η) :
    ‖k‖ * weighted s p ≤ (Fintype.card ι : ℝ) * (C+B) * η := by
  have ht (i : ι) : weighted s (Z i*Q*Z i) ≤ (C+B)*η := by
    calc
      _ = weighted s (Z i*(Q*Z i)) := by rw [Matrix.mul_assoc]
      _ ≤ ‖Z i‖*weighted s (Q*Z i) := weighted_left s _ _
      _ ≤ weighted s (Q*Z i) := by
        exact (mul_le_mul_of_nonneg_right (hZ i) (hsNorm_nonneg _)).trans_eq (one_mul _)
      _ ≤ ‖Z i‖*weighted s Q + ‖Q‖*hs (comm (Z i) s.xi) := weighted_right s _ _
      _ ≤ 1*(C*η) + B*η := add_le_add
        (mul_le_mul (hZ i) hQ (hsNorm_nonneg _) (by norm_num))
        (mul_le_mul hQn (hc i) (hsNorm_nonneg _) hB)
      _ = (C+B)*η := by ring
  rw [← CompilerCertificates.weighted_smul, hidentity]
  classical
  have hsum (t : Finset ι) :
      weighted s (∑ i ∈ t, Z i*Q*Z i) ≤ ∑ i ∈ t, (C+B)*η := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (weighted_add s _ _).trans (add_le_add (ht i) ih)
  simpa [mul_assoc] using hsum Finset.univ

end
end E2.CompilerSelector
