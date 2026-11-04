import E2.FiniteSourceCoordinates

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem sourceDiagonal_one (N k : ℕ) : sourceDiagonal N k (fun _ => 1)=1 := by simp [sourceDiagonal]

theorem sourceDiagonal_add (N k : ℕ) (v w : SourceBasis N k → ℝ) :
    sourceDiagonal N k v+sourceDiagonal N k w=sourceDiagonal N k (fun z => v z+w z) := by
  simp only [sourceDiagonal,Complex.ofReal_add,Matrix.diagonal_add]

theorem sourceDiagonal_sub (N k : ℕ) (v w : SourceBasis N k → ℝ) :
    sourceDiagonal N k v-sourceDiagonal N k w=sourceDiagonal N k (fun z => v z-w z) := by
  simp only [sourceDiagonal,Complex.ofReal_sub,Matrix.diagonal_sub]

theorem sourceDiagonal_one_sub (N k : ℕ) (v : SourceBasis N k → ℝ) :
    1-sourceDiagonal N k v=sourceDiagonal N k (fun z => 1-v z) := by
  rw [←sourceDiagonal_one N k,sourceDiagonal_sub]

theorem sourceDiagonal_mul (N k : ℕ) (v w : SourceBasis N k → ℝ) :
    sourceDiagonal N k v*sourceDiagonal N k w=sourceDiagonal N k (fun z => v z*w z) := by
  simp only [sourceDiagonal,Complex.ofReal_mul,Matrix.diagonal_mul_diagonal]

theorem sourceDiagonal_real_smul (N k : ℕ) (c : ℝ) (v : SourceBasis N k → ℝ) :
    (c:ℂ) • sourceDiagonal N k v=sourceDiagonal N k (fun z => c*v z) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [sourceDiagonal,Matrix.smul_apply,smul_eq_mul]
  · simp [sourceDiagonal,Matrix.diagonal_apply,Matrix.smul_apply,h]

theorem sourceConj_diagonal (N k : ℕ) (s : Equiv.Perm (SourceBasis N k)) (v : SourceBasis N k → ℝ) :
    (sourcePerm N k s).permMatrix ℂ*sourceDiagonal N k v*((sourcePerm N k s).permMatrix ℂ).conjTranspose=
      sourceDiagonal N k (fun z => v (s z)) := by
  rw [sourceDiagonal,perm_conj_diagonal]
  congr 1
  funext i
  rw [sourcePerm_basis]

theorem sourceDiagonal_commute (N k : ℕ) (v w : SourceBasis N k → ℝ) :
    sourceDiagonal N k v*sourceDiagonal N k w=sourceDiagonal N k w*sourceDiagonal N k v := by
  rw [sourceDiagonal_mul,sourceDiagonal_mul]
  congr 1
  funext z
  exact mul_comm _ _

end
end E2.FiniteConstruction