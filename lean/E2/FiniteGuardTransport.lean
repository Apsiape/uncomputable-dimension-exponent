import E2.FiniteGuardRecursion
import E2.FiniteMatrixTransport
import E2.FiniteListClocks

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem realDiagonal_conjTranspose {α : Type*} [DecidableEq α] (v : α → ℝ) :
    (Matrix.diagonal (fun i => (v i:ℂ))).conjTranspose=Matrix.diagonal (fun i => (v i:ℂ)) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [Matrix.conjTranspose_apply]
  · simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,Ne.symm h]

theorem matrixReindex_diagonal {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (v : α → ℂ) :
    matrixReindexStar e (Matrix.diagonal v)=Matrix.diagonal (fun i => v (e.symm i)) := by
  ext i j
  change Matrix.diagonal v (e.symm i) (e.symm j)=Matrix.diagonal (fun i => v (e.symm i)) i j
  by_cases h : i=j
  · subst j; simp
  · simp [Matrix.diagonal_apply,h,e.symm.injective.ne h]

theorem matrixReindex_permutation {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Equiv.Perm α) :
    matrixReindexStar e (s.permMatrix ℂ)=Equiv.Perm.permMatrix ℂ (e.symm.trans (s.trans e)) := by
  rw [←graphMatrix_perm,←graphMatrix_perm]
  ext i j
  change (if s (e.symm i)=e.symm j then (1:ℂ) else 0)=
    (if e (s (e.symm i))=j then 1 else 0)
  by_cases h : e (s (e.symm i))=j
  · have hs : s (e.symm i)=e.symm j := by rw [←h,e.symm_apply_apply]
    simp [h,hs]
  · have hs : s (e.symm i)≠e.symm j := by intro he; apply h; rw [he,e.apply_symm_apply]
    simp [h,hs]

def rawWordCoordinate {β : Type*} [DecidableEq β] (N : ℕ) : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ :=
  Matrix.diagonal (fun z => (listCoordinate z.1.val:ℂ))

theorem raw_coordinate_guard {β : Type*} [DecidableEq β] (N : ℕ) :
    1-rawWordCoordinate (β := β) N=coordinateGuard N := by
  rw [rawWordCoordinate,show (1:Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ)=
    Matrix.diagonal (fun _ => 1) by simp,Matrix.diagonal_sub]
  congr 1
  funext z
  push_cast
  rfl

/-- The original guarded polynomial, before reindexing or dressing. -/
theorem raw_original_guard_norm {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (hN : 0<N) (r : Equiv.Perm β) :
    ‖(((twistedIncrement N r).permMatrix ℂ).conjTranspose-
      (rawWordFlip N).permMatrix ℂ*((1-rawWordDigit N)+
        (rawWordRotation N).permMatrix ℂ*((twistedIncrement N r).permMatrix ℂ).conjTranspose*
          ((rawWordRotation N).permMatrix ℂ).conjTranspose*rawWordDigit N))*
        (1-rawWordCoordinate N)‖ ≤ 2*(1/4:ℝ)^N := by
  let U := (twistedIncrement N r).permMatrix ℂ
  let T : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ := (rawWordRotation N).permMatrix ℂ
  let X : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ := (rawWordFlip N).permMatrix ℂ
  let P := rawWordDigit (β := β) N
  let A := rawWordCoordinate (β := β) N
  let G := (U.conjTranspose-X*((1-P)+T*U.conjTranspose*T.conjTranspose*P))*(1-A)
  have hA : A.conjTranspose=A := realDiagonal_conjTranspose _
  have hP : P.conjTranspose=P := realDiagonal_conjTranspose _
  have hX : X.conjTranspose=X := (reflection_of_involutive (rawWordFlip (β := β) N)
    (prod_involutive _ _ (flipFirstWord_involutive N) (fun _ => rfl))).1
  have he : star G=coordinateGuard N*(U-((1-P)+P*T*U*T.conjTranspose)*X) := by
    change G.conjTranspose=_
    simp only [G,Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_add,
      Matrix.conjTranspose_one,Matrix.conjTranspose_conjTranspose,hA,hP,hX]
    rw [show 1-A=coordinateGuard (β := β) N from raw_coordinate_guard N]
    noncomm_ring
  change ‖G‖≤_
  calc
    _ = ‖star G‖ := (norm_star G).symm
    _ = ‖coordinateGuard N*(U-((1-P)+P*T*U*T.conjTranspose)*X)‖ := congrArg norm he
    _ ≤ 2*(1/4:ℝ)^N := raw_guard_operator_bound N hN r

end
end E2.FiniteConstruction