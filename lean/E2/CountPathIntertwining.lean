import E2.CountNormalization
import E2.CountIntertwining

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

 theorem reverse_word_cons {d m : ℕ} (p : Fin (m+1) → Measurement d)
    (b : Fin (p 0).outcomes) (a : RecordType (fun i => p i.succ)) :
    reverseWord p (Fin.cons b a) = (p 0).projection b * reverseWord (fun i => p i.succ) a := by
  simp only [reverseWord, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]

 theorem reverse_record_cocomplete {d m : ℕ} (p : Fin m → Measurement d) :
    (∑ a : RecordType p, reverseWord p a * (reverseWord p a).conjTranspose) = 1 := by
  simp_rw [reverse_word_adjoint, Matrix.conjTranspose_conjTranspose]
  simpa only [Recording.word, recordingWord, List.ofFn_eq_map] using
    Recording.record_complete (fun i => (p i).projection)
      (fun i => by simpa only [(p i).selfadjoint, (p i).idempotent] using (p i).complete)

 theorem reverse_record_commutator {d m : ℕ} (p : Fin m → Measurement d) (s : State d) :
    Recording.familyNorm (fun a : RecordType p => comm (reverseWord p a) s.xi) ≤
      ∑ i, Recording.familyNorm (fun a => comm ((p i).projection a) s.xi) := by
  have h := Recording.record_commutator (fun i => (p i).projection)
    (fun i => by simpa only [(p i).selfadjoint, (p i).idempotent] using (p i).complete)
    (fun i => by simpa only [(p i).selfadjoint, (p i).idempotent] using (p i).complete) s.xi
  have he (a : RecordType p) : comm (reverseWord p a) s.xi =
      -(comm (recordingWord p a) s.xi).conjTranspose := by
    simp only [reverse_word_adjoint, comm, Companion.Analytic.comm, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, s.xi_positive.isHermitian.eq, neg_sub]
  have hn : Recording.familyNorm (fun a : RecordType p => comm (reverseWord p a) s.xi) =
      Recording.familyNorm (fun a : RecordType p => comm (recordingWord p a) s.xi) := by
    apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _)).mp
    simp only [Recording.familyNorm_sq, he, hs_neg_matrix, hsNorm_conjTranspose]
  rw [hn]
  simpa only [Recording.word, recordingWord, List.ofFn_eq_map] using h

 theorem reverse_column_bound {α : Type*} [Fintype α] {d m : ℕ}
    (s : State d) (p : Fin m → Measurement d) (C : Matrix α (Fin d) ℂ)
    (η a L : ℝ) (hη : 0≤η) (hL : 0≤L)
    (hstate : ∀ i b, hs (comm ((p i).projection b) s.xi)≤η)
    (hcolumn : ‖C‖≤L) (herror : hs (C*s.xi)≤a) :
    Recording.familyNorm (fun b : RecordType p => C*reverseWord p b*s.xi) ≤
      a+L*m*Real.sqrt 3*η := by
  have hcomm := reverse_record_commutator p s
  have hsum : (∑ i, Recording.familyNorm (fun b => comm ((p i).projection b) s.xi)) ≤
      (m:ℝ)*(Real.sqrt 3*η) := by
    calc
      _ ≤ ∑ i : Fin m, Real.sqrt 3*η := Finset.sum_le_sum (fun i _ =>
        Recording.single_commutator_bound _ s.xi η hη
          (by rcases (p i).arity with h | h <;> omega) (hstate i))
      _ = _ := by simp
  calc
    _ ≤ hs (C*s.xi)+‖C‖*Recording.familyNorm (fun b : RecordType p =>
      comm (reverseWord p b) s.xi) :=
        Recording.column_branch_bound _ (reverse_record_cocomplete p) s.xi C
    _ ≤ a+L*((m:ℝ)*(Real.sqrt 3*η)) := add_le_add herror
      (mul_le_mul hcolumn (hcomm.trans hsum) (Recording.familyNorm_nonneg _) hL)
    _ = _ := by ring

/-- Slide one unitary through the complete recording word. The induction
splits off the next adjacent crossing and retains the full suffix record. -/
 theorem reverse_intertwining_path {d m : ℕ} (s : State d) (η : ℝ)
    (p : Fin m → Measurement d) (U : Mat d)
    (σ : ∀ i, Equiv.Perm (Fin (p i).outcomes))
    (hU : Domain.unitary.Holds U) (hη : 0≤η)
    (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi)≤η)
    (hcross : ∀ i a, weighted s (U*(p i).projection a-(p i).projection (σ i a)*U)≤η) :
    Recording.familyNorm (fun a : RecordType p =>
      (U*reverseWord p a-reverseWord p (fun i => σ i (a i))*U)*s.xi) ≤
        (m:ℝ)^2*Real.sqrt 3*η := by
  induction m with
  | zero => simp [reverseWord, Recording.familyNorm, Recording.stack, hsNorm, hsSquared]
  | succ m ih =>
    let tail : Fin m → Measurement d := fun i => p i.succ
    let E (a : RecordType tail) :=
      (U*reverseWord tail a-reverseWord tail (fun i => σ i.succ (a i))*U)*s.xi
    let D (b : Fin (p 0).outcomes) :=
      U*(p 0).projection b-(p 0).projection (σ 0 b)*U
    have hi : Recording.familyNorm E ≤ (m:ℝ)^2*Real.sqrt 3*η :=
      ih tail (fun i => σ i.succ) (fun i => hstate i.succ) (fun i => hcross i.succ)
    have hD : Recording.familyNorm (fun a : RecordType tail =>
        Recording.stack D*reverseWord tail a*s.xi) ≤ Real.sqrt 3*η+2*m*Real.sqrt 3*η := by
      apply reverse_column_bound s tail _ η (Real.sqrt 3*η) 2 hη (by norm_num)
        (fun i => hstate i.succ)
      · exact Recording.intertwining_column_norm (p 0) U hU (σ 0)
      · exact Recording.intertwining_column_error s (p 0) U (σ 0) η hη (hcross 0)
    have heq : Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail =>
        D t.1*reverseWord tail t.2*s.xi) =
        Recording.familyNorm (fun a : RecordType tail => Recording.stack D*reverseWord tail a*s.xi) := by
      apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _)).mp
      simp only [Recording.familyNorm_sq, Fintype.sum_prod_type]
      change (∑ b, ∑ a, hs (D b*reverseWord tail a*s.xi)^2) =
        ∑ a, hs (Recording.stack (fun b => D b*reverseWord tail a*s.xi))^2
      simp only [hsNorm_sq, hsSquared, Recording.stack, Fintype.sum_prod_type]
      exact Finset.sum_comm
    have hP : (∑ b, ((p 0).projection (σ 0 b)).conjTranspose * (p 0).projection (σ 0 b))=1 :=
      Recording.relabel_complete _ (by simpa only [(p 0).selfadjoint, (p 0).idempotent] using (p 0).complete) (σ 0)
    have hleft := Recording.familyNorm_pair_left (fun b => (p 0).projection (σ 0 b)) hP E
    have hreindex := Recording.familyNorm_equiv (Fin.consEquiv (fun i => Fin (p i).outcomes))
      (fun a : RecordType p => (U*reverseWord p a-reverseWord p (fun i => σ i (a i))*U)*s.xi)
    rw [←hreindex]
    have he : (fun t : Fin (p 0).outcomes × RecordType tail =>
        (U*reverseWord p (Fin.cons t.1 t.2)-
          reverseWord p (fun i => σ i ((Fin.cons t.1 t.2 : RecordType p) i))*U)*s.xi) =
        (fun t => D t.1*reverseWord tail t.2*s.xi+(p 0).projection (σ 0 t.1)*E t.2) := by
      funext t
      simp only [reverseWord, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
      dsimp [D, E, tail, reverseWord]
      noncomm_ring
    change Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail =>
      (U*reverseWord p (Fin.cons t.1 t.2)-reverseWord p (fun i => σ i ((Fin.cons t.1 t.2 : RecordType p) i))*U)*s.xi) ≤ _
    rw [he]
    calc
      _ ≤ Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail => D t.1*reverseWord tail t.2*s.xi)+
          Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail => (p 0).projection (σ 0 t.1)*E t.2) :=
        Recording.familyNorm_add _ _
      _ ≤ (Real.sqrt 3*η+2*m*Real.sqrt 3*η)+(m:ℝ)^2*Real.sqrt 3*η := by
        rw [heq, hleft]
        exact add_le_add hD hi
      _ = _ := by push_cast; ring

end
end E2

