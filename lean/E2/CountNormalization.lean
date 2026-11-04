import E2.Turn9.CountClassicalStatements
import E2.LowerTransport

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator

/-- The two recording conventions are adjoints, with every outcome retained. -/
theorem reverse_word_adjoint {d m : ℕ} (p : Fin m → Measurement d) (a : RecordType p) :
    reverseWord p a = (recordingWord p a).conjTranspose := by
  simp only [reverseWord, recordingWord, Matrix.conjTranspose_list_prod,
    List.map_reverse, List.reverse_reverse, ← List.ofFn_eq_map,
    List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact ((p i).selfadjoint (a i)).symm

 theorem reverse_record_complete {d m : ℕ} (p : Fin m → Measurement d) :
    (∑ a : RecordType p, (reverseWord p a).conjTranspose * reverseWord p a) = 1 := by
  simp_rw [reverse_word_adjoint, Matrix.conjTranspose_conjTranspose]
  simpa only [Recording.word, recordingWord, List.ofFn_eq_map] using Recording.record_coComplete (fun i => (p i).projection)
    (fun i => by simpa only [(p i).selfadjoint, (p i).idempotent] using (p i).complete)

 theorem record_normalization : Turn9.RecordNormalization := by
  intro d m s p
  refine ⟨fun a => sq_nonneg _, ?_⟩
  change (∑ a : RecordType p, hs (reverseWord p a * s.xi)^2) = 1
  rw [Recording.parseval_left _ (reverse_record_complete p), state_hs_xi]
  norm_num

end
end E2


