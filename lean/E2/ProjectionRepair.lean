import E2.MatrixFunctions

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

def halfCut (x : ℝ) : ℝ := if 1/2≤x then 1 else 0

theorem halfCut_square (x : ℝ) : halfCut x*halfCut x=halfCut x := by
  unfold halfCut
  split <;> norm_num

theorem halfCut_error (x : ℝ) (hx : 0≤x ∧ x≤1) :
    (halfCut x-x)^2 ≤ x-x*x := by
  unfold halfCut
  split
  · rename_i hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hx.2)]
  · rename_i hh
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hh)))]

theorem halfCut_factor (x : ℝ) : halfCut x=x*(halfCut x/x) := by
  by_cases hx : x=0
  · subst x
    norm_num [halfCut]
  · field_simp

theorem spectral_round_projection {d : ℕ} (A : Mat d) (hA : A.IsHermitian) :
    Domain.projection.Holds (matrixFunction halfCut A) := by
  refine ⟨(matrix_function_hermitian hA halfCut).eq,?_⟩
  rw [matrix_function_mul]
  apply matrix_function_congr hA
  intro x hx
  exact halfCut_square x

theorem spectral_round_supported {d : ℕ} (F A : Mat d) (hA : A.IsHermitian)
    (hFA : F*A=A) : F*matrixFunction halfCut A=matrixFunction halfCut A := by
  have hfactor : matrixFunction halfCut A=A*matrixFunction (fun x => halfCut x/x) A := by
    calc
      _ = matrixFunction (fun x => x*(halfCut x/x)) A :=
        matrix_function_congr hA _ _ (fun x _ => halfCut_factor x)
      _ = matrixFunction id A*matrixFunction (fun x => halfCut x/x) A :=
        (matrix_function_mul _ _ _).symm
      _ = _ := by rw [matrix_function_id hA]
  rw [hfactor,← Matrix.mul_assoc,hFA]

theorem spectral_round_gram {d : ℕ} (hd : 0<d) (A : Mat d) (hpos : A.PosSemidef) (hnorm : ‖A‖≤1) :
    (A-A*A-(matrixFunction halfCut A-A).conjTranspose*(matrixFunction halfCut A-A)).PosSemidef := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  let hA := hpos.isHermitian
  have hd : matrixFunction halfCut A-A=matrixFunction (fun x => halfCut x-x) A := by
    calc
      _ = matrixFunction halfCut A-matrixFunction id A := by rw [matrix_function_id hA]
      _ = _ := matrix_function_sub _ _ _
  have haa : A*A=matrixFunction (fun x => x*x) A := by
    calc
      A*A=matrixFunction id A*matrixFunction id A := by rw [matrix_function_id hA]
      _ = _ := matrix_function_mul _ _ _
  have ha : A-A*A=matrixFunction (fun x => x-x*x) A := by
    rw [haa]
    calc
      _ = matrixFunction id A-matrixFunction (fun x => x*x) A := by rw [matrix_function_id hA]
      _ = _ := matrix_function_sub _ _ _
  have he : (matrixFunction halfCut A-A).IsHermitian := (matrix_function_hermitian hA _).sub hA
  rw [he.eq,hd,ha,matrix_function_mul,matrix_function_sub]
  apply matrix_function_positive hA
  intro i
  have hlo := hpos.eigenvalues_nonneg i
  have hhi : hA.eigenvalues i≤1 :=
    (Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)).trans hnorm)
  have h := halfCut_error (hA.eigenvalues i) ⟨hlo,hhi⟩
  nlinarith

/-- Exact inclusion repair from Lemma 9.3, on the original, possibly non-flat
state. The repaired operator is the threshold of FQF, never a new tensor factor. -/
theorem projection_inclusion_repair {d : ℕ} (s : State d) (hd : 0<d)
    (F Q : Mat d) (hF : Domain.projection.Holds F) (hQ : Domain.projection.Holds Q)
    (η : ℝ) (hη : 0≤η) (hinc : weighted s ((1-F)*Q)≤η)
    (hFs : hs (comm F s.xi)≤η) (hQs : hs (comm Q s.xi)≤η) :
    ∃ R : Mat d, Domain.projection.Holds R ∧ F*R=R ∧ weighted s (R-Q)≤6*η := by
  let A := F*Q*F
  let L := (1-F)*Q*F
  let r := (1-F)*Q
  let R := matrixFunction halfCut A
  have hnF := projection_norm_le hF
  have hnQ := projection_norm_le hQ
  have hFc := projection_complement hF
  have hnFc := projection_norm_le hFc
  have hnr : ‖r‖≤1 := by
    calc
      _ ≤ ‖1-F‖*‖Q‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul hnFc hnQ (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hFcstate : hs (comm (1-F) s.xi)≤η := by
    have he : comm (1-F) s.xi= -comm F s.xi := by
      simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
      abel
    rw [he,hs_neg_matrix]
    exact hFs
  have hrstate : hs (comm r s.xi)≤2*η := by
    have h := word_state_commutator s hd η hη [1-F,Q]
      (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl <;> assumption)
      (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl <;> assumption)
    simpa [r] using h
  have hqA : weighted s (Q-A)≤4*η := by
    have he : Q-A=r+F*r.conjTranspose := by
      dsimp [A,r]
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hF.1,hQ.1]
      noncomm_ring
    rw [he]
    calc
      _ ≤ weighted s r+weighted s (F*r.conjTranspose) := weighted_add _ _ _
      _ ≤ weighted s r+‖F‖*weighted s r.conjTranspose := add_le_add (le_refl _) (weighted_left _ _ _)
      _ ≤ weighted s r+1*weighted s r.conjTranspose :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hnF (hsNorm_nonneg _))
      _ ≤ weighted s r+(weighted s r+hs (comm r s.xi)) := by
        rw [one_mul]
        exact add_le_add (le_refl _) (weighted_adjoint s r)
      _ ≤ 4*η := by linarith
  have hL : weighted s L≤2*η := by
    calc
      _ ≤ ‖F‖*weighted s r+‖r‖*hs (comm F s.xi) := weighted_right s F r
      _ ≤ 1*η+1*η := by
        gcongr <;> first | exact hsNorm_nonneg _ | exact hnF | exact hinc | exact hnr | exact hFs
      _ = 2*η := by ring
  have hApos : A.PosSemidef := by
    simpa only [hF.1] using (projection_positive hQ).conjTranspose_mul_mul_same F
  have hAnorm : ‖A‖≤1 := by
    calc
      _ ≤ ‖F*Q‖*‖F‖ := norm_mul_le _ _
      _ ≤ (‖F‖*‖Q‖)*‖F‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1*1)*1 := by gcongr
      _ = 1 := by norm_num
  have hFA : F*A=A := by
    dsimp [A]
    simp only [← Matrix.mul_assoc,hF.2]
  have hAA : A*A=F*Q*F*Q*F := by
    change (F*Q*F)*(F*Q*F)=_
    calc
      _ = F*Q*(F*F)*Q*F := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hF.2]
  have hgram : L.conjTranspose*L=A-A*A := by
    calc
      _ = F*Q*((1-F)*(1-F))*Q*F := by
        dsimp [L]
        simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,
          hF.1,hQ.1,Matrix.mul_assoc]
      _ = F*Q*(1-F)*Q*F := by rw [hFc.2]
      _ = F*(Q*Q)*F-F*Q*F*Q*F := by
        simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.mul_assoc]
      _ = _ := by rw [hQ.2,hAA]
  have hRA : weighted s (R-A)≤2*η := by
    have hpos := spectral_round_gram hd A hApos hAnorm
    rw [← hgram] at hpos
    exact (hs_gram_mono (R-A) L s.xi hpos).trans hL
  refine ⟨R,spectral_round_projection A hApos.isHermitian,spectral_round_supported F A hApos.isHermitian hFA,?_⟩
  have he : (R-Q)*s.xi=(R-A)*s.xi-(Q-A)*s.xi := by
    simp only [Matrix.sub_mul]
    abel
  unfold weighted
  rw [he]
  exact (hs_sub_le _ _).trans (by change weighted s (R-A)+weighted s (Q-A)≤6*η; linarith)

end
end E2
