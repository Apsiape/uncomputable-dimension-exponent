import E2.CompilerDuplication

namespace E2.CompilerTensor
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open E2.FiniteConstruction E2.CompilerRealification Companion.Analytic
variable {n d : ℕ}

def tensor (A : Mat n) (B : Mat d) : Mat (n*d) :=
  matrixReindexStar (finProdFinEquiv : Fin n × Fin d ≃ Fin (n*d)) (Matrix.kronecker A B)

@[simp] theorem tensor_mul (A C : Mat n) (B D : Mat d) :
    tensor (A*C) (B*D)=tensor A B*tensor C D := by
  simp only [tensor,Matrix.kronecker,Matrix.mul_kronecker_mul,map_mul]
@[simp] theorem tensor_one : tensor (1:Mat n) (1:Mat d)=1 := by
  simp only [tensor,Matrix.kronecker,Matrix.one_kronecker_one,map_one]
@[simp] theorem tensor_star (A : Mat n) (B : Mat d) :
    tensor (star A) (star B)=star (tensor A B) := by
  unfold tensor
  rw [← map_star]
  congr 1
  exact (Matrix.conjTranspose_kronecker A B).symm

def source (n : ℕ) (B : Mat d) : Mat (n*d) := tensor 1 B

def selector (d : ℕ) (A : Mat n) : Mat (n*d) := tensor A 1

@[simp] theorem source_one : source n (1:Mat d)=1 := tensor_one
@[simp] theorem source_mul (A B : Mat d) : source n (A*B)=source n A*source n B := by
  simpa only [source,one_mul] using tensor_mul (1:Mat n) 1 A B
@[simp] theorem source_star (A : Mat d) : source n (star A)=star (source n A) := by
  simpa only [source,star_one] using tensor_star (1:Mat n) A
@[simp] theorem source_add (A B : Mat d) : source n (A+B)=source n A+source n B := by
  simp only [source,tensor,Matrix.kronecker,Matrix.kronecker_add,map_add]
@[simp] theorem source_smul (c : ℂ) (A : Mat d) : source n (c • A)=c • source n A := by
  simp only [source,tensor,Matrix.kronecker,Matrix.kronecker_smul,map_smul]
@[simp] theorem source_zero : source n (0:Mat d)=0 := by
  simpa only [zero_smul] using source_smul (n:=n) (d:=d) 0 1
@[simp] theorem source_neg (A : Mat d) : source n (-A) = -source n A := by
  simpa only [neg_one_smul] using source_smul (n:=n) (-1) A
@[simp] theorem source_sub (A B : Mat d) : source n (A-B)=source n A-source n B := by
  simp only [sub_eq_add_neg,source_add,source_neg]

theorem source_selector_commute (A : Mat n) (B : Mat d) :
    Commute (source n B) (selector d A) := by
  change tensor 1 B*tensor A 1=tensor A 1*tensor 1 B
  rw [← tensor_mul,← tensor_mul]
  simp

theorem tensor_reflection (A : Mat n) (B : Mat d)
    (hA : Domain.reflection.Holds A) (hB : Domain.reflection.Holds B) :
    Domain.reflection.Holds (tensor A B) := by
  constructor
  · change star (tensor A B)=tensor A B
    rw [← tensor_star,show star A=A from hA.1,show star B=B from hB.1]
  · rw [← tensor_mul,hA.2,hB.2,tensor_one]

theorem source_reflection (B : Mat d) (hB : Domain.reflection.Holds B) :
    Domain.reflection.Holds (source n B) := tensor_reflection 1 B ⟨by simp,by simp⟩ hB

theorem trace_tensor (A : Mat n) (B : Mat d) : (tensor A B).trace=A.trace*B.trace := by
  rw [tensor,trace_reindex]
  exact Matrix.trace_kronecker A B

theorem hs_source_square (B : Mat d) : hs (source n B)^2=(n:ℝ)*hs B^2 := by
  rw [hsNorm_sq,hsSquared_trace,hsNorm_sq,hsSquared_trace]
  change ((star (source n B)*source n B).trace).re = _
  rw [← source_star,← source_mul,source,trace_tensor]
  simp [Matrix.star_eq_conjTranspose]

theorem weighted_source (hn : 0<n) (hd : 0<d) (B : Mat d) :
    weighted (flatState (n*d) (Nat.mul_pos hn hd)) (source n B) = weighted (flatState d hd) B := by
  have he : weighted (flatState (n*d) (Nat.mul_pos hn hd)) (source n B)^2 =
      weighted (flatState d hd) B^2 := by
    rw [CompilerFlat.flat_state_weighted_square,CompilerFlat.flat_state_weighted_square,
      hs_source_square]
    have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    push_cast
    field_simp
  exact (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp he

theorem eval_source {ι : Type*} (x : ι → Mat d) (p : Poly ι) :
    Poly.eval (fun i => source n (x i)) p=source n (Poly.eval x p) := by
  induction p <;> simp_all [Poly.eval,← Matrix.star_eq_conjTranspose]

end
end E2.CompilerTensor
