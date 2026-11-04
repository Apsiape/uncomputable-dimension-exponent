import E2.FiniteBitClock
import E2.Source

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 150000

noncomputable def wordBasis (N : ℕ) : Fin (2^N) ≃ Bits N :=
  Fintype.equivOfCardEq (by simp [Bits])

def wordPerm (N : ℕ) (σ : Equiv.Perm (Bits N)) : Equiv.Perm (Fin (2^N)) :=
  (wordBasis N).trans (σ.trans (wordBasis N).symm)

theorem wordPerm_basis (N : ℕ) (σ : Equiv.Perm (Bits N)) (i : Fin (2^N)) :
    wordBasis N (wordPerm N σ i)=σ (wordBasis N i) := by simp [wordPerm]

def finiteA (N : ℕ) : Mat (2^N) :=
  Matrix.diagonal (fun i => (coordinate (wordBasis N i):ℂ))

def finiteP (n : ℕ) : Mat (2^(n+1)) :=
  Matrix.diagonal (fun i => (bit (wordBasis (n+1) i) 0:ℂ))

def finiteT (N : ℕ) : Mat (2^N) := (wordPerm N (rotateWord N)).permMatrix ℂ

def finiteX (n : ℕ) : Mat (2^(n+1)) := (wordPerm (n+1) (flipWord 0)).permMatrix ℂ

theorem finiteA_domain (N : ℕ) : Domain.positiveContraction.Holds (finiteA N) := by
  exact diagonal_positive_contraction _ (fun i => coordinate_bounds _)

theorem finiteP_domain (n : ℕ) : Domain.projection.Holds (finiteP n) := by
  simpa only [Domain.Holds,finiteP,bit,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using
    diagonal_projection (fun i => wordBasis (n+1) i 0)

theorem finiteT_domain (N : ℕ) : Domain.unitary.Holds (finiteT N) := perm_unitary _

theorem finiteX_domain (n : ℕ) : Domain.reflection.Holds (finiteX n) := by
  have hstar : (finiteX n).conjTranspose=finiteX n := by
    rw [finiteX,Matrix.conjTranspose_permMatrix]
    congr 1
  have hu : (finiteX n).conjTranspose*finiteX n=1 := (perm_unitary (wordPerm (n+1) (flipWord 0))).1
  rw [hstar] at hu
  exact ⟨hstar,hu⟩

theorem finite_AP (n : ℕ) : finiteA (n+1)*finiteP n-finiteP n*finiteA (n+1)=0 := by
  simp only [finiteA,finiteP,Matrix.diagonal_mul_diagonal]
  have he : (fun i => (coordinate (wordBasis (n+1) i):ℂ)*(bit (wordBasis (n+1) i) 0:ℂ))=
      (fun i => (bit (wordBasis (n+1) i) 0:ℂ)*(coordinate (wordBasis (n+1) i):ℂ)) := by
    funext i; ring
  rw [he,sub_self]

theorem finite_own_flip (n : ℕ) : finiteX n*finiteP n*finiteX n=1-finiteP n := by
  have hc := perm_conj_diagonal (wordPerm (n+1) (flipWord 0))
    (fun i => (bit (wordBasis (n+1) i) 0:ℂ))
  change finiteX n*finiteP n*(finiteX n).conjTranspose=_ at hc
  rw [(finiteX_domain n).1] at hc
  rw [hc]
  have he : (fun i => (bit (wordBasis (n+1) (wordPerm (n+1) (flipWord 0) i)) 0:ℂ))=
      (fun i => 1-(bit (wordBasis (n+1) i) 0:ℂ)) := by
    funext i
    rw [wordPerm_basis,flip_bit_same]
    push_cast
    rfl
  rw [he]
  change Matrix.diagonal (fun i => 1-(bit (wordBasis (n+1) i) 0:ℂ))=
    1-Matrix.diagonal (fun i => (bit (wordBasis (n+1) i) 0:ℂ))
  rw [←Matrix.diagonal_sub,Matrix.diagonal_one]

theorem finite_affine (n : ℕ) :
    finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose-
      ((4:ℂ) • finiteA (n+1)-(3:ℂ) • finiteP n)=
      ((3*(1/4:ℝ)^(n+1):ℝ):ℂ) • finiteP n := by
  rw [finiteT,finiteA,perm_conj_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.diagonal_apply_eq,
      finiteA,finiteP,smul_eq_mul]
    rw [wordPerm_basis]
    have h := rotate_coordinate n (wordBasis (n+1) i)
    have hr : coordinate (rotateWord (n+1) (wordBasis (n+1) i))-
      (4*coordinate (wordBasis (n+1) i)-3*bit (wordBasis (n+1) i) 0)=
      3*(1/4:ℝ)^(n+1)*bit (wordBasis (n+1) i) 0 := by linarith
    have hc := congrArg (fun x : ℝ => (x:ℂ)) hr
    push_cast at hc ⊢
    exact hc
  · simp [finiteA,finiteP,Matrix.diagonal_apply,hij]

theorem finite_affine_norm (n : ℕ) :
    ‖finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose-
      ((4:ℂ) • finiteA (n+1)-(3:ℂ) • finiteP n)‖≤3*(1/4:ℝ)^(n+1) := by
  rw [finite_affine,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hp : ‖finiteP n‖≤1 := by
    rw [finiteP,Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (bit_bounds _ _).1]
    exact (bit_bounds _ _).2
  nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0≤3*(1/4:ℝ)^(n+1))]


theorem finite_tail_norm (n : ℕ) :
    ‖finiteX n*(finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose)-
      (finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose)*finiteX n‖≤
      3*(1/4:ℝ)^(n+1) := by
  simp only [finiteT,finiteA,perm_conj_diagonal]
  apply perm_comm_diagonal_norm _ _ _ (by positivity)
  intro i
  simp only [wordPerm_basis]
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,rotate_flip_coordinate]
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*(1/4:ℝ)^(n+1))]
  have hb : |1-2*bit (wordBasis (n+1) i) 0|=1 := by
    cases h : wordBasis (n+1) i 0 <;> norm_num [bit,h]
  rw [hb,mul_one]

end
end E2.FiniteConstruction
