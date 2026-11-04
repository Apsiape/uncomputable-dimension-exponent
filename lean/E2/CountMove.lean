import E2.CountMoveHelpers

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 400000

/-- Each induction step moves the selected projector across the next earlier
projector. The error column is evaluated on every record of the remaining word. -/
 theorem move_to_end_estimate {d m : ℕ} (s : State d) (η : ℝ)
    (p : Fin m → Measurement d) (hη : 0≤η)
    (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi)≤η)
    (hcomm : ∀ i j, i≠j → ∀ a b, weighted s (comm ((p i).projection a) ((p j).projection b))≤η) :
    ∀ i : Fin m, Recording.familyNorm (fun a : RecordType p =>
      (reverseWord p a-movedWord p i a)*s.xi) ≤ 3*(m:ℝ)^2*η := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ k ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have he (b : Fin (p 0).outcomes) (a : RecordType (fun j => p j.succ)) :
          reverseWord p (Fin.cons b a)=movedWord p 0 (Fin.cons b a) := by
        rw [reverse_word_cons]
        change _ = (p 0).projection b * erasedWord p 0 (Fin.cons b a)
        rw [erased_word_cons_zero]
      have hreindex := Recording.familyNorm_equiv (Fin.consEquiv (fun j => Fin (p j).outcomes))
        (fun a : RecordType p => (reverseWord p a-movedWord p 0 a)*s.xi)
      rw [←hreindex]
      change Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType (fun j => p j.succ) =>
        (reverseWord p (Fin.cons t.1 t.2)-movedWord p 0 (Fin.cons t.1 t.2))*s.xi)≤_
      simp only [he, sub_self, Matrix.zero_mul]
      have hz : Recording.familyNorm (fun _t : Fin (p 0).outcomes × RecordType (fun j => p j.succ) => (0:Mat d))=0 := by
        simp [Recording.familyNorm, Recording.stack, hsNorm, hsSquared]
      rw [hz]
      positivity
    · cases k with
      | zero => exact Fin.elim0 j
      | succ n =>
        let tail : Fin (n+1) → Measurement d := fun j => p j.succ
        let rest : Fin n → Measurement d := fun k => tail (j.succAbove k)
        let E (a : RecordType tail) := (reverseWord tail a-movedWord tail j a)*s.xi
        let D (t : Fin (p 0).outcomes × Fin (tail j).outcomes) :=
          comm ((p 0).projection t.1) ((tail j).projection t.2)
        have hi : Recording.familyNorm E≤3*((n+1:ℕ):ℝ)^2*η :=
          ih tail (fun k => hstate k.succ)
            (fun k l h => hcomm k.succ l.succ (fun he => h (Fin.succ_injective _ he))) j
        have hD : Recording.familyNorm (fun a : RecordType rest =>
            Recording.stack D*reverseWord rest a*s.xi)≤3*η+2*n*Real.sqrt 3*η := by
          apply reverse_column_bound s rest _ η (3*η) 2 hη (by norm_num)
            (fun k => hstate (j.succAbove k).succ)
          · exact Recording.commutator_column_norm _ _
              (by simpa only [(p 0).selfadjoint, (p 0).idempotent] using (p 0).complete)
              (by simpa only [(tail j).selfadjoint, (tail j).idempotent] using (tail j).complete)
          · exact Recording.pair_commutator_error s η (p 0) (tail j) hη
              (hcomm 0 j.succ (Ne.symm (Fin.succ_ne_zero _)))
        have herror : Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail =>
            D (t.1,t.2 j)*erasedWord tail j t.2*s.xi) =
            Recording.familyNorm (fun a : RecordType rest => Recording.stack D*reverseWord rest a*s.xi) := by
          apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _)).mp
          rw [Recording.familyNorm_sq, Recording.familyNorm_sq, Fintype.sum_prod_type]
          simp_rw [sum_records_pivot tail j]
          simp only [erased_word_reindex, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
          have hstack (a : RecordType rest) :
              hs (Recording.stack D*reverseWord rest a*s.xi)^2 =
                ∑ b : Fin (p 0).outcomes, ∑ c : Fin (tail j).outcomes, hs (D (b,c)*reverseWord rest a*s.xi)^2 := by
            change Recording.familyNorm (fun t : Fin (p 0).outcomes × Fin (tail j).outcomes =>
              D t*reverseWord rest a*s.xi)^2=_
            rw [Recording.familyNorm_sq, Fintype.sum_prod_type]
          simp_rw [hstack]
          change (∑ b : Fin (p 0).outcomes, ∑ c : Fin (tail j).outcomes, ∑ a : RecordType rest,
            hs (D (b,c)*reverseWord rest a*s.xi)^2) =
              ∑ a : RecordType rest, ∑ b : Fin (p 0).outcomes, ∑ c : Fin (tail j).outcomes,
                hs (D (b,c)*reverseWord rest a*s.xi)^2
          calc
            _ = ∑ b : Fin (p 0).outcomes, ∑ a : RecordType rest, ∑ c : Fin (tail j).outcomes,
                hs (D (b,c)*reverseWord rest a*s.xi)^2 := by
              apply Finset.sum_congr rfl
              intro b _
              exact Finset.sum_comm
            _ = _ := Finset.sum_comm
        have hP : (∑ b, ((p 0).projection b).conjTranspose*(p 0).projection b)=1 := by
          simpa only [(p 0).selfadjoint, (p 0).idempotent] using (p 0).complete
        have hleft := Recording.familyNorm_pair_left (p 0).projection hP E
        have hreindex := Recording.familyNorm_equiv (Fin.consEquiv (fun j => Fin (p j).outcomes))
          (fun a : RecordType p => (reverseWord p a-movedWord p j.succ a)*s.xi)
        rw [←hreindex]
        change Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail =>
          (reverseWord p (Fin.cons t.1 t.2)-movedWord p j.succ (Fin.cons t.1 t.2))*s.xi)≤_
        have he : (fun t : Fin (p 0).outcomes × RecordType tail =>
            (reverseWord p (Fin.cons t.1 t.2)-movedWord p j.succ (Fin.cons t.1 t.2))*s.xi) =
            (fun t => (p 0).projection t.1*E t.2+D (t.1,t.2 j)*erasedWord tail j t.2*s.xi) := by
          funext t
          rw [reverse_word_cons]
          change ((p 0).projection t.1*reverseWord tail t.2-
            (tail j).projection (t.2 j)*erasedWord p j.succ (Fin.cons t.1 t.2))*s.xi=_
          rw [erased_word_cons_succ]
          dsimp [E, D, movedWord, erasedWord, comm, Companion.Analytic.comm, tail]
          noncomm_ring
        rw [he]
        calc
          _ ≤ Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail => (p 0).projection t.1*E t.2)+
              Recording.familyNorm (fun t : Fin (p 0).outcomes × RecordType tail => D (t.1,t.2 j)*erasedWord tail j t.2*s.xi) :=
            Recording.familyNorm_add _ _
          _ ≤ 3*((n+1:ℕ):ℝ)^2*η+(3*η+2*n*Real.sqrt 3*η) := by
            rw [hleft, herror]
            exact add_le_add hi hD
          _ ≤ 3*((n+1+1:ℕ):ℝ)^2*η := by
            have hroot : Real.sqrt 3≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3), Real.sqrt_nonneg 3]
            have hn : (0:ℝ)≤n := Nat.cast_nonneg n
            have hr := mul_le_mul_of_nonneg_left hroot (show (0:ℝ)≤2*n*η by positivity)
            push_cast
            nlinarith [mul_nonneg hn hη]

 theorem move_to_end_vector : Turn9.MoveToEndVector := by
  exact ⟨3, by norm_num, fun _ _ s η p hη hstate hcomm => move_to_end_estimate s η p hη hstate hcomm⟩

 theorem decoder_error_bound : Turn9.DecoderErrorBound := by
  refine ⟨9, by norm_num, ?_⟩
  intro d m s η p hη hstate hcomm i
  have h := decoder_from_recording_distance s p i (3*(m:ℝ)^2*η) (by positivity)
    (move_to_end_estimate s η p hη hstate hcomm i)
  convert h using 1 <;> ring

end
end E2
