import E2.CountFanoMeasurement

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder

theorem projection_factor_trace {d : ℕ} (P L : Mat d) (hP : Domain.projection.Holds P) :
    (L*L.conjTranspose*P).trace.re = hs (P*L)^2 := by
  rw [hs_square_gram, hP.1,hP.2]
  congr 1
  calc
    _ = (P*(L*L.conjTranspose)).trace := Matrix.trace_mul_comm _ _
    _ = ((P*L)*L.conjTranspose).trace := by simp only [Matrix.mul_assoc]
    _ = (L.conjTranspose*(P*L)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem projection_factor_split {d : ℕ} (P L : Mat d) (hP : Domain.projection.Holds P) :
    hs (P*L)^2+hs ((1-P)*L)^2=hs L^2 := by
  have hc := projection_complement hP
  rw [hs_square_gram, hs_square_gram, hP.1,hP.2,hc.1,hc.2]
  have he : L.conjTranspose*P*L+L.conjTranspose*(1-P)*L=L.conjTranspose*L := by noncomm_ring
  rw [←Complex.add_re,←Matrix.trace_add,he]
  simpa using (hs_square_gram (1 : Mat d) L).symm

theorem record_density_factor {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) :
    recordDensity s p a = (reverseWord p a*s.xi)*(reverseWord p a*s.xi).conjTranspose := by
  rw [recordDensity, Matrix.conjTranspose_mul,s.xi_positive.isHermitian.eq,←s.xi_square]
  simp only [Matrix.mul_assoc]

theorem decoder_joint_error {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) :
    let F := (CountCQ.record s p).coarse (fun a => a i)
    (∑ b,∑ a∈Finset.univ.erase b,F.joint (CountCQ.decoder (p i)) a b) = decodeFailure s p i := by
  classical
  let F := (CountCQ.record s p).coarse (fun a => a i)
  let P := CountCQ.decoder (p i)
  have hj (a b : Fin (p i).outcomes) : F.joint P a b =
      ∑ r : RecordType p,if r i=a then hs ((p i).projection b*reverseWord p r*s.xi)^2 else 0 := by
    unfold CountCQ.Family.joint
    change ( (∑ r : RecordType p, if r i=a then recordDensity s p r else 0) * (p i).projection b).trace.re = _
    rw [Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs
    · rw [record_density_factor,projection_factor_trace _ _ ⟨(p i).selfadjoint b,(p i).idempotent b⟩]
      simp only [Matrix.mul_assoc]
    · simp
  have hsuccess : (∑ b,F.joint P b b)=
      ∑ r : RecordType p,hs ((p i).projection (r i)*reverseWord p r*s.xi)^2 := by
    simp_rw [hj]
    rw [Finset.sum_comm]
    simp
  have hsplit : (∑ r : RecordType p,hs ((p i).projection (r i)*reverseWord p r*s.xi)^2)+decodeFailure s p i=1 := by
    rw [decodeFailure,←Finset.sum_add_distrib]
    have he (r : RecordType p) :
        hs ((p i).projection (r i)*reverseWord p r*s.xi)^2+
        hs ((1-(p i).projection (r i))*reverseWord p r*s.xi)^2=recordMass s p r := by
      simpa only [recordMass,Matrix.mul_assoc] using projection_factor_split ((p i).projection (r i))
        (reverseWord p r*s.xi) ⟨(p i).selfadjoint (r i),(p i).idempotent (r i)⟩
    simp_rw [he]
    exact (record_normalization d m s p).2
  have hcol (b : Fin (p i).outcomes) :
      (∑ a∈Finset.univ.erase b,F.joint P a b)+F.joint P b b=∑ a,F.joint P a b :=
    Finset.sum_erase_add _ _ (Finset.mem_univ b)
  have hsum := congrArg (fun f : Fin (p i).outcomes → ℝ => ∑ b,f b) (funext hcol)
  rw [Finset.sum_add_distrib,F.joint_total P,hsuccess] at hsum
  linarith

theorem quantum_fano : Turn9.QuantumFano := by
  intro d m s p i e he0 hehalf herror
  let F := (CountCQ.record s p).coarse (fun a => a i)
  have hn : (p i).outcomes≤3 := by rcases (p i).arity with h | h <;> omega
  have hf := F.fano (CountCQ.decoder (p i)) hn (CountCQ.original s)
  rw [CountCQ.marginal_conditional,decoder_joint_error] at hf
  have hnon : 0≤decodeFailure s p i := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact hf.trans (add_le_add (binary_entropy_mono_half hnon hehalf herror) herror)

end
end E2

