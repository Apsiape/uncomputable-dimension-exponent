import E2.CompilerExtensions
import E2.FiniteMatrixTransport

/-! Flatten the displayed two-by-two block gadgets into the original `Mat`
type in exactly twice the dimension. -/
namespace E2.CompilerBlocks
noncomputable section
open scoped BigOperators
variable {d : ℕ}

def flatten (M : Block (Mat d)) : Matrix (Fin 2 × Fin d) (Fin 2 × Fin d) ℂ :=
  fun i j => M i.1 j.1 i.2 j.2

@[simp] theorem flatten_add (M N : Block (Mat d)) : flatten (M+N)=flatten M+flatten N := rfl
@[simp] theorem flatten_zero : flatten (0 : Block (Mat d))=0 := rfl
@[simp] theorem flatten_mul (M N : Block (Mat d)) : flatten (M*N)=flatten M*flatten N := by
  ext i j
  simp [flatten,Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_apply]

@[simp] theorem flatten_one : flatten (1 : Block (Mat d))=1 := by
  ext i j
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  by_cases hij : i=j <;> by_cases hab : a=b <;>
    simp [flatten,Matrix.one_apply,hij,hab,Prod.ext_iff]

@[simp] theorem flatten_star (M : Block (Mat d)) : flatten (star M)=star (flatten M) := rfl

def doubleMatrix (M : Block (Mat d)) : Mat (2*d) :=
  E2.FiniteConstruction.matrixReindexStar (finProdFinEquiv : Fin 2 × Fin d ≃ Fin (2*d)) (flatten M)

@[simp] theorem doubleMatrix_mul (M N : Block (Mat d)) : doubleMatrix (M*N)=doubleMatrix M*doubleMatrix N := by
  simp [doubleMatrix]
@[simp] theorem doubleMatrix_one : doubleMatrix (1 : Block (Mat d))=1 := by simp [doubleMatrix]
@[simp] theorem doubleMatrix_star (M : Block (Mat d)) : doubleMatrix (star M)=star (doubleMatrix M) := by
  unfold doubleMatrix
  rw [flatten_star]
  exact map_star _ _

theorem doubleMatrix_reflection (M : Block (Mat d)) (hM : Reflection M) :
    Domain.reflection.Holds (doubleMatrix M) := by
  constructor
  · change star (doubleMatrix M)=doubleMatrix M
    rw [← doubleMatrix_star,hM.1]
  · rw [← doubleMatrix_mul,hM.2,doubleMatrix_one]

theorem doubleMatrix_parity (M N P : Block (Mat d)) (h : ParityTriple M N P) :
    ParityTriple (doubleMatrix M) (doubleMatrix N) (doubleMatrix P) := by
  rcases h with ⟨hMN,hMP,hNP,hprod⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [← doubleMatrix_mul,← doubleMatrix_mul,hMN]
  · rw [← doubleMatrix_mul,← doubleMatrix_mul,hMP]
  · rw [← doubleMatrix_mul,← doubleMatrix_mul,hNP]
  · rw [← doubleMatrix_mul,← doubleMatrix_mul,hprod,doubleMatrix_one]

/-- The six-context extension in the actual matrix dimension, not merely a
formal block algebra. It has exactly a factor-two overhead. -/
theorem six_extension_matrices (a b c : Mat d)
    (ha : Domain.reflection.Holds a) (hb : Domain.reflection.Holds b)
    (hc : Domain.reflection.Holds c) (hrel : a*b*a=c) (hbc : b*c=c*b) :
    ∃ D : Fin 7 → Mat (2*d),
      (∀ i, Domain.reflection.Holds (D i)) ∧
      ParityTriple (doubleMatrix (diag a a)) (D 0) (D 1) ∧
      ParityTriple (doubleMatrix (diag b b)) (D 1) (D 2) ∧
      ParityTriple (D 2) (D 3) (D 4) ∧
      ParityTriple (doubleMatrix (diag a a)) (D 4) (D 5) ∧
      ParityTriple (doubleMatrix (diag c c)) (D 5) (D 6) ∧
      ParityTriple (D 0) (D 3) (D 6) := by
  have h := six_extension a b c ha hb hc hrel hbc
  exact ⟨fun i => doubleMatrix (sixExtension a b c i),
    fun i => doubleMatrix_reflection _ (h.1 i),
    doubleMatrix_parity _ _ _ h.2.1,
    doubleMatrix_parity _ _ _ h.2.2.1,
    doubleMatrix_parity _ _ _ h.2.2.2.1,
    doubleMatrix_parity _ _ _ h.2.2.2.2.1,
    doubleMatrix_parity _ _ _ h.2.2.2.2.2.1,
    doubleMatrix_parity _ _ _ h.2.2.2.2.2.2⟩

end
end E2.CompilerBlocks
