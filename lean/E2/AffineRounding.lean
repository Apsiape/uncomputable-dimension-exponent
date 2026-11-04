import E2.AffineCompression

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The quarter-sized Cantor distance is absorbed before any digit is read.
The output stays on the original Hilbert space and the original state. -/
theorem affine_cantor_rounding {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hA : Domain.positiveContraction.Holds c.A)
    (hP : Domain.projection.Holds c.P) (hT : Domain.unitary.Holds c.T)
    (hAP : weighted s (comm c.A c.P)≤δ)
    (hAff : weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))≤δ)
    (hσA : hs (comm c.A s.xi)≤δ) (hσP : hs (comm c.P s.xi)≤δ)
    (hσT : hs (comm c.T s.xi)≤δ) :
    ∃ Ahat : Mat d, HasCantorSpectrum Ahat ∧ weighted s (Ahat-c.A)≤150*δ ∧
      hs (comm Ahat s.xi)≤301*δ ∧ weighted s (c.P-matrixFunction digitFunction Ahat)≤414*δ := by
  have hd := state_dimension_pos s
  letI : NeZero d := ⟨ne_of_gt hd⟩
  obtain ⟨D,hD,hDP,hDB,hσD,hC,hσC⟩ :=
    affine_block_estimates s δ c hδ hA hP hT hAP hAff hσA hσP hσT
  let B := c.T*c.A*c.T.conjTranspose
  let C := blockAffine D c.P
  let f := fun x => Metric.infDist x cantorSet
  let FA := matrixFunction f c.A
  let FB := matrixFunction f B
  let FC := matrixFunction f C
  let FD := matrixFunction f D
  have hCh : C.IsHermitian := blockAffine_hermitian D c.P hD.1.isHermitian hP
  have hBh : B.IsHermitian := unitary_conjugate_hermitian c.T c.A hA.1.isHermitian
  have hAC : weighted s (c.A-C)≤11*δ := by rw [weighted_sub_symm]; exact hC
  have hBD : weighted s (B-D)≤42*δ := by rw [weighted_sub_symm]; exact hDB
  have hFAC : weighted s (FA-FC)≤57*δ := by
    have h := weighted_functional_calculus s c.A C f 1 hA.1.isHermitian hCh cantor_distance_lipschitz.lipschitzOnWith
    norm_num at h
    change weighted s (FA-FC)≤weighted s (c.A-C)+2*hs (comm C s.xi) at h
    nlinarith
  have hFDB : weighted s (FD-FB)≤216*δ := by
    have h := weighted_functional_calculus s B D f 1 hBh hD.1.isHermitian cantor_distance_lipschitz.lipschitzOnWith
    norm_num at h
    change weighted s (FB-FD)≤weighted s (B-D)+2*hs (comm D s.xi) at h
    rw [weighted_sub_symm] at h
    nlinarith
  have hscale : weighted s FC=(1/4)*weighted s FD := by
    change weighted s (matrixFunction (fun x => Metric.infDist x cantorSet) (blockAffine D c.P))=
      (1/4)*weighted s (matrixFunction (fun x => Metric.infDist x cantorSet) D)
    rw [blockAffine_distance D c.P hD hP hDP,weighted_smul]
    norm_num
  have hnFA : ‖FA‖≤1 := by
    apply matrix_function_norm_bound c.A f 1 (by norm_num)
    intro x hx
    change |Metric.infDist x cantorSet|≤1
    rw [abs_of_nonneg Metric.infDist_nonneg]
    exact cantor_distance_unit (positive_contraction_spectrum c.A hA x hx)
  have hFBT : FB=c.T*FA*c.T.conjTranspose :=
    (matrix_function_conjugate c.T c.A hT hA.1.isHermitian f).symm
  have hFB : weighted s FB≤weighted s FA+δ := by
    have h := unitary_weighted_transport s c.T.conjTranspose FA (unitary_adjoint hT)
    simp only [Matrix.conjTranspose_conjTranspose,unitary_adjoint_state_commutator s c.T hT] at h
    have hm := mul_le_mul hnFA hσT (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤1)
    rw [hFBT]
    nlinarith
  have htriA := weighted_add s (FA-FC) FC
  have htriD := weighted_add s (FD-FB) FB
  rw [sub_add_cancel] at htriA htriD
  have hdist : weighted s FA≤150*δ := by nlinarith
  let Ahat := matrixFunction cantorRound c.A
  have hr := cantor_spectral_rounding s c.A hA.1.isHermitian
  have hspec : HasCantorSpectrum Ahat := hr.1
  have hclose : weighted s (Ahat-c.A)≤150*δ := by
    change weighted s (matrixFunction cantorRound c.A-c.A)≤150*δ
    rw [hr.2.1]
    exact hdist
  have hσ : hs (comm Ahat s.xi)≤301*δ := hr.2.2.trans (by nlinarith)
  have hnewC : weighted s (Ahat-C)≤161*δ := by
    calc
      _=weighted s ((Ahat-c.A)+(c.A-C)) := by congr 1; abel
      _≤weighted s (Ahat-c.A)+weighted s (c.A-C) := weighted_add _ _ _
      _≤_ := by linarith
  have hp := weighted_functional_calculus s Ahat C digitFunction 2 hspec.1 hCh digitFunction_lipschitz.lipschitzOnWith
  norm_num at hp
  have hpc : matrixFunction digitFunction C=c.P := blockAffine_digit D c.P hD hP hDP
  rw [hpc] at hp
  have hbase : weighted s (c.P-matrixFunction digitFunction Ahat)≤414*δ := by
    rw [weighted_sub_symm]
    nlinarith
  exact ⟨Ahat,hspec,hclose,hσ,hbase⟩

end
end E2

#print axioms E2.affine_cantor_rounding
