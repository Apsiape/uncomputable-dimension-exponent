import E2.Weighted

/-! Finite-family HS calculus for Section 8. The Parseval and family-norm
arguments port the corresponding audited finite-dimensional calculations in
the companion's ReadoutHellinger/BranchHilbertSchmidt/BranchComposition files.
They are proved here for arbitrary finite outcome alphabets and rectangular
matrices; there is no dependency on the active companion checkout. -/
namespace E2.Recording
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator

def stack {ι α β : Type*} (A : ι → Matrix α β ℂ) : Matrix (ι × α) β ℂ :=
  fun x j => A x.1 x.2 j

def familyNorm {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : ℝ := hs (stack A)

theorem familyNorm_nonneg {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : 0≤familyNorm A := hsNorm_nonneg _

theorem familyNorm_sq {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : familyNorm A^2=∑ i, hs (A i)^2 := by
  simp only [familyNorm,hsNorm_sq,hsSquared,stack,Fintype.sum_prod_type]

theorem familyNorm_add {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A B : ι → Matrix α β ℂ) :
    familyNorm (fun i => A i+B i)≤familyNorm A+familyNorm B := hsNorm_add_le _ _

theorem familyNorm_equiv {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (e : ι ≃ κ) (A : κ → Matrix α β ℂ) : familyNorm (A ∘ e)=familyNorm A := by
  apply (sq_eq_sq₀ (familyNorm_nonneg _) (familyNorm_nonneg _)).mp
  simp only [familyNorm_sq,Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem familyNorm_conjTranspose {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : familyNorm (fun i => (A i).conjTranspose)=familyNorm A := by
  apply (sq_eq_sq₀ (familyNorm_nonneg _) (familyNorm_nonneg _)).mp
  simp only [familyNorm_sq,hsNorm_conjTranspose]

theorem parseval_left {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq α]
    (P : ι → Matrix α α ℂ) (hP : ∑ i, (P i).conjTranspose*P i=1) (A : Matrix α β ℂ) :
    (∑ i, hs (P i*A)^2)=hs A^2 := by
  simp_rw [hsNorm_sq,hsSquared_trace]
  have he : (∑ i, (P i*A).conjTranspose*(P i*A))=A.conjTranspose*A := by
    calc
      _=A.conjTranspose*(∑ i, (P i).conjTranspose*P i)*A := by
        simp only [Matrix.conjTranspose_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
      _=_ := by rw [hP,Matrix.mul_one]
  have h := congrArg (fun X : Matrix β β ℂ => X.trace.re) he
  simpa only [Matrix.trace_sum,Complex.re_sum] using h

theorem parseval_right {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] [DecidableEq β]
    (P : ι → Matrix β β ℂ) (hP : ∑ i, P i*(P i).conjTranspose=1) (A : Matrix α β ℂ) :
    (∑ i, hs (A*P i)^2)=hs A^2 := by
  have h := parseval_left (fun i => (P i).conjTranspose) (by simpa using hP) A.conjTranspose
  simpa only [←Matrix.conjTranspose_mul,hsNorm_conjTranspose] using h

theorem familyNorm_pair_left {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq α] (P : ι → Matrix α α ℂ) (hP : ∑ i, (P i).conjTranspose*P i=1)
    (A : κ → Matrix α β ℂ) : familyNorm (fun t : ι × κ => P t.1*A t.2)=familyNorm A := by
  apply (sq_eq_sq₀ (familyNorm_nonneg _) (familyNorm_nonneg _)).mp
  rw [familyNorm_sq,familyNorm_sq,Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [parseval_left P hP]

theorem familyNorm_pair_right {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    [DecidableEq β] (P : ι → Matrix β β ℂ) (hP : ∑ i, P i*(P i).conjTranspose=1)
    (A : κ → Matrix α β ℂ) : familyNorm (fun t : κ × ι => A t.1*P t.2)=familyNorm A := by
  apply (sq_eq_sq₀ (familyNorm_nonneg _) (familyNorm_nonneg _)).mp
  simp_rw [familyNorm_sq,Fintype.sum_prod_type,parseval_right P hP]

def vecColumn {α β : Type*} (A : Matrix α β ℂ) (j : β) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun i => A i j)

theorem hs_sq_columns {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) :
    hs A^2=∑ j, ‖vecColumn A j‖^2 := by
  simp only [hsNorm_sq,hsSquared,vecColumn,EuclideanSpace.norm_sq_eq,Complex.normSq_eq_norm_sq]
  exact Finset.sum_comm

/-- The actual rectangular column operator norm, not its Frobenius norm. -/
theorem rectangular_mul_bound {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] (C : Matrix α β ℂ) (A : Matrix β γ ℂ) : hs (C*A)≤‖C‖*hs A := by
  have hj (j : γ) : ‖vecColumn (C*A) j‖≤‖C‖*‖vecColumn A j‖ := by
    exact Matrix.l2_opNorm_mulVec C (vecColumn A j)
  have hsq : hs (C*A)^2≤(‖C‖*hs A)^2 := by
    rw [hs_sq_columns]
    calc
      _≤∑ j, (‖C‖*‖vecColumn A j‖)^2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2)
      _=‖C‖^2*(∑ j, ‖vecColumn A j‖^2) := by simp only [mul_pow,Finset.mul_sum]
      _=(‖C‖*hs A)^2 := by rw [←hs_sq_columns]; ring
  exact (sq_le_sq₀ (hsNorm_nonneg _) (mul_nonneg (norm_nonneg _) (hsNorm_nonneg _))).mp hsq

theorem familyNorm_rectangular_mul {ι α β γ : Type*} [Fintype ι] [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] (C : Matrix α β ℂ) (A : ι → Matrix β γ ℂ) :
    familyNorm (fun i => C*A i)≤‖C‖*familyNorm A := by
  have hsq : familyNorm (fun i => C*A i)^2≤(‖C‖*familyNorm A)^2 := by
    rw [familyNorm_sq]
    calc
      _≤∑ i, (‖C‖*hs (A i))^2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hsNorm_nonneg _) (rectangular_mul_bound C (A i)) 2)
      _=‖C‖^2*(∑ i, hs (A i)^2) := by simp only [mul_pow,Finset.mul_sum]
      _=_ := by rw [←familyNorm_sq]; ring
  exact (sq_le_sq₀ (familyNorm_nonneg _) (mul_nonneg (norm_nonneg _) (familyNorm_nonneg _))).mp hsq

end
end E2.Recording
