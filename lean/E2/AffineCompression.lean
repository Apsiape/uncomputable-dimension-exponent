import E2.SpectralBlocks
import E2.CarryRoutingTools

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

def blockCompress {d : ℕ} (B P : Mat d) : Mat d := P*B*P+(1-P)*B*(1-P)

theorem blockCompress_contraction {d : ℕ} (B P : Mat d)
    (hB : Domain.positiveContraction.Holds B) (hP : Domain.projection.Holds P) :
    Domain.positiveContraction.Holds (blockCompress B P) := by
  have hQ := projection_complement hP
  have hpos (H : Mat d) (hh : H.PosSemidef) : (blockCompress H P).PosSemidef := by
    have hp : (P*H*P).PosSemidef := by simpa only [hP.1] using hh.conjTranspose_mul_mul_same P
    have hq : ((1-P)*H*(1-P)).PosSemidef := by
      have h := hh.conjTranspose_mul_mul_same (1-P)
      rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hP.1] at h
      exact h
    exact hp.add hq
  refine ⟨hpos B hB.1,?_⟩
  have he : blockCompress (1-B) P=1-blockCompress B P := by
    calc
      _=(P*P-P*B*P)+((1-P)*(1-P)-(1-P)*B*(1-P)) := by dsimp [blockCompress]; noncomm_ring
      _=_ := by rw [hP.2,hQ.2]; dsimp [blockCompress]; abel
  rw [←he]
  exact hpos (1-B) hB.2

theorem blockCompress_commutes {d : ℕ} (B P : Mat d) (hP : Domain.projection.Holds P) :
    blockCompress B P*P=P*blockCompress B P := by
  have hPQ : P*(1-P)=0 := by rw [Matrix.mul_sub,Matrix.mul_one,hP.2,sub_self]
  have hQP : (1-P)*P=0 := by rw [Matrix.sub_mul,Matrix.one_mul,hP.2,sub_self]
  have hl : P*blockCompress B P=P*B*P := by
    calc
      _=(P*P)*B*P+(P*(1-P))*B*(1-P) := by simp only [blockCompress,Matrix.mul_add,Matrix.mul_assoc]
      _=_ := by rw [hP.2,hPQ]; simp
  have hr : blockCompress B P*P=P*B*P := by
    calc
      _=P*B*(P*P)+(1-P)*B*((1-P)*P) := by simp only [blockCompress,Matrix.add_mul,Matrix.mul_assoc]
      _=_ := by rw [hP.2,hQP]; simp
  exact hr.trans hl.symm

theorem blockCompress_error {d : ℕ} (B P : Mat d) (hP : Domain.projection.Holds P) :
    B-blockCompress B P=(P+P-1)*comm P B := by
  symm
  calc
    _=(P*P)*B+(P*P)*B-P*B*P-P*B*P-P*B+B*P := by
      simp only [comm,Companion.Analytic.comm]
      noncomm_ring
    _=P*B+B*P-P*B*P-P*B*P := by rw [hP.2]; abel
    _=_ := by dsimp [blockCompress]; noncomm_ring

theorem selfadjoint_state_comparison {d : ℕ} (s : State d) (A B : Mat d)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hs (comm A s.xi)≤hs (comm B s.xi)+2*weighted s (A-B) := by
  have he : comm A s.xi=comm B s.xi+comm (A-B) s.xi := by
    simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub]
    abel
  rw [he]
  exact (hsNorm_add_le _ _).trans (add_le_add le_rfl (selfadjoint_state_commutator s _ (hA.sub hB)))

/-- Explicit constants for the block step of Lemma 4.2, using only the affine
clock relations. All estimates are on the original state. -/
theorem affine_block_estimates {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hA : Domain.positiveContraction.Holds c.A)
    (hP : Domain.projection.Holds c.P) (hT : Domain.unitary.Holds c.T)
    (hAP : weighted s (comm c.A c.P)≤δ)
    (hAff : weighted s (c.T*c.A*c.T.conjTranspose-((4:ℂ) • c.A-(3:ℂ) • c.P))≤δ)
    (hσA : hs (comm c.A s.xi)≤δ) (hσP : hs (comm c.P s.xi)≤δ)
    (hσT : hs (comm c.T s.xi)≤δ) :
    ∃ D : Mat d, Domain.positiveContraction.Holds D ∧ D*c.P=c.P*D ∧
      weighted s (D-c.T*c.A*c.T.conjTranspose)≤42*δ ∧ hs (comm D s.xi)≤87*δ ∧
      weighted s (blockAffine D c.P-c.A)≤11*δ ∧ hs (comm (blockAffine D c.P) s.xi)≤23*δ := by
  have hd := state_dimension_pos s
  letI : NeZero d := ⟨ne_of_gt hd⟩
  let B := c.T*c.A*c.T.conjTranspose
  let D := blockCompress B c.P
  let E := B-((4:ℂ) • c.A-(3:ℂ) • c.P)
  have hB : Domain.positiveContraction.Holds B := by
    refine ⟨?_,?_⟩
    · simpa only [B,Matrix.conjTranspose_conjTranspose] using hA.1.conjTranspose_mul_mul_same c.T.conjTranspose
    · have he : 1-B=c.T*(1-c.A)*c.T.conjTranspose := by
        simp only [B,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hT.2]
      rw [he]
      simpa only [Matrix.conjTranspose_conjTranspose] using hA.2.conjTranspose_mul_mul_same c.T.conjTranspose
  have hD : Domain.positiveContraction.Holds D := blockCompress_contraction B c.P hB hP
  have hDP : D*c.P=c.P*D := blockCompress_commutes B c.P hP
  have hnA := positive_contraction_norm hA
  have hnB := positive_contraction_norm hB
  have hnP := projection_norm_le hP
  have hnT : ‖c.T‖≤1 := (unitary_norm hd hT).le
  have hnT' : ‖c.T.conjTranspose‖≤1 := (unitary_norm hd (unitary_adjoint hT)).le
  have hσT' : hs (comm c.T.conjTranspose s.xi)≤δ := by
    rw [unitary_adjoint_state_commutator s c.T hT]
    exact hσT
  have hσB : hs (comm B s.xi)≤3*δ := by
    have h := word_state_commutator s hd δ hδ [c.T,c.A,c.T.conjTranspose]
      (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl | rfl <;> assumption)
      (by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl | rfl | rfl <;> assumption)
    simpa [B,Matrix.mul_assoc] using h
  have hnF : ‖(4:ℂ) • c.A-(3:ℂ) • c.P‖≤7 := by
    have h := norm_sub_le ((4:ℂ) • c.A) ((3:ℂ) • c.P)
    simp only [norm_smul] at h
    norm_num at h
    nlinarith
  have hnE : ‖E‖≤8 := (norm_sub_le _ _).trans (by linarith)
  have hEP : weighted s (comm E c.P)≤10*δ := by
    have h := commutator_replace s E c.P hnP
    have hm := mul_le_mul hnE hσP (hsNorm_nonneg _) (by norm_num : (0:ℝ)≤8)
    have hE : weighted s E≤δ := hAff
    nlinarith
  have hBP : weighted s (comm B c.P)≤14*δ := by
    have he : comm B c.P=comm E c.P+(4:ℂ) • comm c.A c.P := by
      dsimp [E]
      simp only [comm,Companion.Analytic.comm,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul]
      module
    rw [he]
    have h := weighted_add s (comm E c.P) ((4:ℂ) • comm c.A c.P)
    rw [weighted_smul] at h
    norm_num at h
    linarith
  have hPB : weighted s (comm c.P B)≤14*δ := by rw [weighted_comm_symm]; exact hBP
  have hnR : ‖c.P+c.P-1‖≤3 := by
    have h := (norm_sub_le (c.P+c.P) (1:Mat d)).trans
      (add_le_add (norm_add_le c.P c.P) (le_refl _))
    norm_num at h
    linarith
  have hDB : weighted s (D-B)≤42*δ := by
    rw [weighted_sub_symm,show B-D=(c.P+c.P-1)*comm c.P B from blockCompress_error B c.P hP]
    exact (weighted_left _ _ _).trans (by
      have h := mul_le_mul hnR hPB (weighted_nonneg _ _) (by norm_num : (0:ℝ)≤3)
      nlinarith)
  have hσD : hs (comm D s.xi)≤87*δ :=
    (selfadjoint_state_comparison s D B hD.1.isHermitian hB.1.isHermitian).trans (by linarith)
  have hC : weighted s (blockAffine D c.P-c.A)≤11*δ := by
    have he : blockAffine D c.P-c.A=(1/4:ℂ) • (D-B)+(1/4:ℂ) • E := by
      dsimp [blockAffine,E]
      module
    rw [he]
    have h := weighted_add s ((1/4:ℂ) • (D-B)) ((1/4:ℂ) • E)
    simp only [weighted_smul] at h
    norm_num at h
    have hE : weighted s E≤δ := hAff
    nlinarith
  have hσC : hs (comm (blockAffine D c.P) s.xi)≤23*δ :=
    (selfadjoint_state_comparison s _ c.A (blockAffine_hermitian D c.P hD.1.isHermitian hP) hA.1.isHermitian).trans (by linarith)
  exact ⟨D,hD,hDP,hDB,hσD,hC,hσC⟩

end
end E2

#print axioms E2.blockCompress
#print axioms E2.blockCompress_contraction
#print axioms E2.blockCompress_commutes
#print axioms E2.blockCompress_error
#print axioms E2.selfadjoint_state_comparison
#print axioms E2.affine_block_estimates
