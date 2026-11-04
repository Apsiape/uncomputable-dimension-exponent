import E2.Turn9.CountPathsStatements

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

/-- In the reordered recording the selected measurement is exactly last. -/
theorem moved_word_decodes {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m) (a : RecordType p) :
    (1-(p i).projection (a i))*movedWord p i a=0 := by
  unfold movedWord
  rw [←Matrix.mul_assoc,Matrix.sub_mul,Matrix.one_mul,(p i).idempotent,sub_self,Matrix.zero_mul]

/-- Apply the same failure projection on the final ORIGINAL system to the
recording-vector difference. This is the quadratic decoder-error step. -/
theorem decoder_from_recording_distance {d m : ℕ} (s : State d)
    (p : Fin m → Measurement d) (i : Fin m) (α : ℝ) (hα : 0≤α)
    (h : Recording.familyNorm (fun a : RecordType p =>
      (reverseWord p a-movedWord p i a)*s.xi)≤α) :
    decodeFailure s p i≤α^2 := by
  have hpoint (a : RecordType p) :
      hs ((1-(p i).projection (a i))*reverseWord p a*s.xi)≤
        hs ((reverseWord p a-movedWord p i a)*s.xi) := by
    have hP : Domain.projection.Holds ((p i).projection (a i)) :=
      ⟨(p i).selfadjoint _,(p i).idempotent _⟩
    have he : (1-(p i).projection (a i))*reverseWord p a*s.xi=
        (1-(p i).projection (a i))*((reverseWord p a-movedWord p i a)*s.xi) := by
      symm
      rw [←Matrix.mul_assoc,Matrix.mul_sub,moved_word_decodes,
        Matrix.sub_mul,Matrix.zero_mul,sub_zero]
    rw [he]
    exact (operator_mul_hs _ _).trans (by
      have hn := projection_norm_le (projection_complement hP)
      nlinarith [hsNorm_nonneg ((reverseWord p a-movedWord p i a)*s.xi)])
  unfold decodeFailure
  calc
    _≤∑ a : RecordType p, hs ((reverseWord p a-movedWord p i a)*s.xi)^2 :=
      Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (hsNorm_nonneg _) (hpoint a) 2)
    _=(Recording.familyNorm (fun a : RecordType p => (reverseWord p a-movedWord p i a)*s.xi))^2 :=
      (Recording.familyNorm_sq _).symm
    _≤α^2 := pow_le_pow_left₀ (Recording.familyNorm_nonneg _) h 2

end
end E2

