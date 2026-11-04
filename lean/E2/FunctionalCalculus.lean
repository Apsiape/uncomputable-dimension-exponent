import E2.HSFunctionalCalculus

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator
open Companion.Analytic

/-- Lemma 2.3, rectangular Hilbert-Schmidt Lipschitz inequality. -/
theorem hs_functional_calculus {d a : ℕ} (A : Mat d) (B : Mat a)
    (Z : Matrix (Fin d) (Fin a) ℂ) (g : ℝ → ℝ) (L : NNReal)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hg : LipschitzOnWith L g (spectrum ℝ A ∪ spectrum ℝ B)) :
    hs (matrixFunction g A * Z - Z * matrixFunction g B) ≤
      L * hs (A*Z-Z*B) :=
  hs_spectral_lipschitz A B Z g L hA hB hg

theorem state_functional_calculus {d : ℕ} (s : State d) (A : Mat d)
    (g : ℝ → ℝ) (L : NNReal) (hA : A.IsHermitian)
    (hg : LipschitzOnWith L g (spectrum ℝ A)) :
    hs (comm (matrixFunction g A) s.xi) ≤ L*hs (comm A s.xi) := by
  have hg' : LipschitzOnWith L g (spectrum ℝ A ∪ spectrum ℝ A) := by simpa using hg
  exact hs_functional_calculus A A s.xi g L hA hA hg'

theorem weighted_functional_calculus {d : ℕ} (s : State d) (A B : Mat d)
    (g : ℝ → ℝ) (L : NNReal) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hg : LipschitzOnWith L g (spectrum ℝ A ∪ spectrum ℝ B)) :
    weighted s (matrixFunction g A-matrixFunction g B) ≤
      L*(weighted s (A-B)+2*hs (comm B s.xi)) := by
  have hgB : LipschitzOnWith L g (spectrum ℝ B) := hg.mono Set.subset_union_right
  have he : (matrixFunction g A-matrixFunction g B)*s.xi =
      (matrixFunction g A*s.xi-s.xi*matrixFunction g B)-comm (matrixFunction g B) s.xi := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul]
    abel
  have hi : hs (A*s.xi-s.xi*B) ≤ weighted s (A-B)+hs (comm B s.xi) := by
    have hid : A*s.xi-s.xi*B=(A-B)*s.xi+comm B s.xi := by
      simp only [comm,Companion.Analytic.comm,Matrix.sub_mul]
      abel
    rw [hid]
    exact hsNorm_add_le _ _
  unfold weighted
  rw [he]
  calc
    _ ≤ hs (matrixFunction g A*s.xi-s.xi*matrixFunction g B)+hs (comm (matrixFunction g B) s.xi) := hs_sub_le _ _
    _ ≤ (L:ℝ)*hs (A*s.xi-s.xi*B)+(L:ℝ)*hs (comm B s.xi) :=
      add_le_add (hs_functional_calculus A B s.xi g L hA hB hg)
        (state_functional_calculus s B g L hB hgB)
    _ ≤ (L:ℝ)*(weighted s (A-B)+hs (comm B s.xi))+(L:ℝ)*hs (comm B s.xi) :=
      add_le_add (mul_le_mul_of_nonneg_left hi L.coe_nonneg) (le_refl _)
    _ = _ := by unfold weighted; ring

theorem commutator_functional_calculus {d : ℕ} (s : State d) (A Y : Mat d)
    (g : ℝ → ℝ) (L : NNReal) (hA : A.IsHermitian) (hY : ‖Y‖ ≤ 1)
    (hg : LipschitzOnWith L g (spectrum ℝ A)) :
    weighted s (comm Y (matrixFunction g A)) ≤
      L*(weighted s (comm Y A)+2*hs (comm A s.xi)) := by
  have hc (Z : Mat d) : hs (Y*Z) ≤ hs Z := by
    calc
      _ ≤ ‖Y‖*hs Z := operator_mul_hs _ _
      _ ≤ 1*hs Z := mul_le_mul_of_nonneg_right hY (hsNorm_nonneg _)
      _ = _ := one_mul _
  have hg' : LipschitzOnWith L g (spectrum ℝ A ∪ spectrum ℝ A) := by simpa using hg
  have he : comm Y (matrixFunction g A)*s.xi =
      Y*comm (matrixFunction g A) s.xi -
        (matrixFunction g A*(Y*s.xi)-(Y*s.xi)*matrixFunction g A) := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  have hi : hs (A*(Y*s.xi)-(Y*s.xi)*A) ≤ hs (comm A s.xi)+weighted s (comm Y A) := by
    have hid : A*(Y*s.xi)-(Y*s.xi)*A=Y*comm A s.xi-comm Y A*s.xi := by
      simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
      abel
    rw [hid]
    exact (hs_sub_le _ _).trans (add_le_add (hc _) (le_refl _))
  unfold weighted
  rw [he]
  calc
    _ ≤ hs (Y*comm (matrixFunction g A) s.xi)+
        hs (matrixFunction g A*(Y*s.xi)-(Y*s.xi)*matrixFunction g A) := hs_sub_le _ _
    _ ≤ (L:ℝ)*hs (comm A s.xi)+(L:ℝ)*hs (A*(Y*s.xi)-(Y*s.xi)*A) :=
      add_le_add ((hc _).trans (state_functional_calculus s A g L hA hg))
        (hs_functional_calculus A A (Y*s.xi) g L hA hA hg')
    _ ≤ (L:ℝ)*hs (comm A s.xi)+(L:ℝ)*(hs (comm A s.xi)+weighted s (comm Y A)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hi L.coe_nonneg)
    _ = _ := by unfold weighted; ring

end
end E2
