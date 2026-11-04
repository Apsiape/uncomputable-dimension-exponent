import E2.CompilerSourceExtension

namespace E2.CompilerBlocks
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open E2.CompilerRealification E2.FiniteConstruction Companion.Analytic
variable {d : ℕ}

def duplicate (M : Mat d) : Mat (2*d) := doubleMatrix (diag M M)

@[simp] theorem duplicate_one : duplicate (1 : Mat d) = 1 := by simp [duplicate]
@[simp] theorem duplicate_zero : duplicate (0 : Mat d) = 0 := by
  have he : diag (0:Mat d) 0=0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
  simp only [duplicate,he,doubleMatrix,flatten_zero,map_zero]
@[simp] theorem duplicate_mul (M N : Mat d) : duplicate (M*N)=duplicate M*duplicate N := by
  simp only [duplicate,← doubleMatrix_mul,diag_mul_diag]
@[simp] theorem duplicate_star (M : Mat d) : duplicate (star M)=star (duplicate M) := by
  simp only [duplicate,← doubleMatrix_star,star_diag]
@[simp] theorem duplicate_add (M N : Mat d) : duplicate (M+N)=duplicate M+duplicate N := by
  have he : diag (M+N) (M+N)=diag M M+diag N N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
  simp only [duplicate,he,doubleMatrix,flatten_add,map_add]
@[simp] theorem duplicate_smul (c : ℂ) (M : Mat d) : duplicate (c • M)=c • duplicate M := by
  have he : diag (c • M) (c • M)=c • diag M M := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
  simp only [duplicate,he,doubleMatrix,flatten_smul,map_smul]
@[simp] theorem duplicate_neg (M : Mat d) : duplicate (-M) = -duplicate M := by
  simpa only [neg_one_smul] using duplicate_smul (-1) M
@[simp] theorem duplicate_sub (M N : Mat d) : duplicate (M-N)=duplicate M-duplicate N := by
  simp only [sub_eq_add_neg,duplicate_add,duplicate_neg]

theorem duplicate_positive (M : Mat d) (hM : M.PosSemidef) : (duplicate M).PosSemidef := by
  let S := QIT.psdSqrt M
  have hs : S.conjTranspose*S=M := by
    rw [(QIT.psdSqrt_isHermitian M).eq]
    exact QIT.psdSqrt_mul_self_of_posSemidef hM
  rw [← hs,duplicate_mul]
  change (duplicate (star S)*duplicate S).PosSemidef
  rw [duplicate_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem duplicate_domain (D : Domain) (M : Mat d) (hM : D.Holds M) : D.Holds (duplicate M) := by
  cases D with
  | positiveContraction =>
    exact ⟨duplicate_positive M hM.1,by simpa using duplicate_positive (1-M) hM.2⟩
  | projection =>
    constructor
    · change star (duplicate M)=duplicate M
      rw [← duplicate_star]; exact congrArg duplicate hM.1
    · rw [← duplicate_mul,hM.2]
  | reflection => exact doubleMatrix_reflection _ (reflection_diag hM hM)
  | unitary =>
    constructor
    · change star (duplicate M)*duplicate M=1
      rw [← duplicate_star,← duplicate_mul]
      change duplicate (M.conjTranspose*M)=1
      rw [hM.1,duplicate_one]
    · change duplicate M*star (duplicate M)=1
      rw [← duplicate_star,← duplicate_mul]
      change duplicate (M*M.conjTranspose)=1
      rw [hM.2,duplicate_one]

theorem duplicate_parity (M N P : Mat d) (h : ParityTriple M N P) :
    ParityTriple (duplicate M) (duplicate N) (duplicate P) := by
  rcases h with ⟨hmn,hmp,hnp,hprod⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [← duplicate_mul,← duplicate_mul,hmn]
  · rw [← duplicate_mul,← duplicate_mul,hmp]
  · rw [← duplicate_mul,← duplicate_mul,hnp]
  · rw [← duplicate_mul,← duplicate_mul,hprod,duplicate_one]

theorem trace_duplicate (M : Mat d) : (duplicate M).trace = 2*M.trace := by
  rw [duplicate,trace_double]
  simp [diag,two_mul]

theorem hs_duplicate_square (M : Mat d) : hs (duplicate M)^2=2*hs M^2 := by
  rw [hsNorm_sq,hsSquared_trace,hsNorm_sq,hsSquared_trace]
  change ((star (duplicate M)*duplicate M).trace).re = _
  rw [← duplicate_star,← duplicate_mul,trace_duplicate]
  simp [Matrix.star_eq_conjTranspose]

theorem weighted_duplicate (hd : 0<d) (M : Mat d) :
    weighted (flatState (2*d) (by omega)) (duplicate M)=weighted (flatState d hd) M := by
  have he : weighted (flatState (2*d) (by omega)) (duplicate M)^2 = weighted (flatState d hd) M^2 := by
    rw [CompilerFlat.flat_state_weighted_square,CompilerFlat.flat_state_weighted_square,
      hs_duplicate_square]
    push_cast
    field_simp
  exact (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp he

theorem eval_duplicate {ι : Type*} (x : ι → Mat d) (p : Poly ι) :
    Poly.eval (fun i => duplicate (x i)) p=duplicate (Poly.eval x p) := by
  induction p <;> simp_all [Poly.eval,← Matrix.star_eq_conjTranspose]

end
end E2.CompilerBlocks
