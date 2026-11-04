import E2.CountColumns

namespace E2.Recording
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

 theorem unitary_left_complete {ι : Type*} [Fintype ι] {d : ℕ}
    (P : ι → Mat d) (hP : ∑ a, (P a).conjTranspose*P a=1)
    (U : Mat d) (hU : Domain.unitary.Holds U) :
    (∑ a, (U*P a).conjTranspose*(U*P a))=1 := by
  simpa only [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc U.conjTranspose U,
    hU.1,Matrix.one_mul] using hP

 theorem unitary_right_complete {ι : Type*} [Fintype ι] {d : ℕ}
    (P : ι → Mat d) (hP : ∑ a, (P a).conjTranspose*P a=1)
    (U : Mat d) (hU : Domain.unitary.Holds U) :
    (∑ a, (P a*U).conjTranspose*(P a*U))=1 := by
  calc
    _=U.conjTranspose*(∑ a, (P a).conjTranspose*P a)*U := by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_assoc]
    _=1 := by rw [hP,Matrix.mul_one,hU.1]

 theorem relabel_complete {ι : Type*} [Fintype ι] {d : ℕ}
    (P : ι → Mat d) (hP : ∑ a, (P a).conjTranspose*P a=1) (σ : Equiv.Perm ι) :
    (∑ a, (P (σ a)).conjTranspose*P (σ a))=1 := by
  exact (Fintype.sum_equiv σ _ _ (fun _ => rfl)).trans hP

 theorem intertwining_column_norm {d : ℕ} (P : Measurement d) (U : Mat d)
    (hU : Domain.unitary.Holds U) (σ : Equiv.Perm (Fin P.outcomes)) :
    ‖stack (fun a => U*P.projection a-P.projection (σ a)*U)‖≤2 := by
  have hP : (∑ a, (P.projection a).conjTranspose*P.projection a)=1 := by
    simpa only [P.selfadjoint,P.idempotent] using P.complete
  exact difference_column_norm _ _ (unitary_left_complete _ hP U hU)
    (unitary_right_complete _ (relabel_complete _ hP σ) U hU)

 theorem intertwining_column_error {d : ℕ} (s : State d) (P : Measurement d) (U : Mat d)
    (σ : Equiv.Perm (Fin P.outcomes)) (η : ℝ) (hη : 0≤η)
    (h : ∀ a, weighted s (U*P.projection a-P.projection (σ a)*U)≤η) :
    familyNorm (fun a => (U*P.projection a-P.projection (σ a)*U)*s.xi)≤Real.sqrt 3*η := by
  have hn : P.outcomes≤3 := by rcases P.arity with h | h <;> omega
  have hs : familyNorm (fun a => (U*P.projection a-P.projection (σ a)*U)*s.xi)^2≤3*η^2 := by
    rw [familyNorm_sq]
    calc
      _≤∑ _a : Fin P.outcomes, η^2 :=
        Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (hsNorm_nonneg _) (h a) 2)
      _=(P.outcomes:ℝ)*η^2 := by simp
      _≤3*η^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (sq_nonneg η)
  apply (sq_le_sq₀ (familyNorm_nonneg _) (by positivity : 0≤Real.sqrt 3*η)).mp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

/-- An own-label swap or later-measurement preservation, after any prefix.
Only the stated intertwiner is needed; U need not be a reflection. -/
 theorem intertwining_after_prefix {d m : ℕ} (s : State d) (η : ℝ)
    (pre : Fin m → Measurement d) (P : Measurement d) (U : Mat d)
    (σ : Equiv.Perm (Fin P.outcomes)) (hU : Domain.unitary.Holds U) (hη : 0≤η)
    (hstate : ∀ i a, hs (comm ((pre i).projection a) s.xi)≤η)
    (h : ∀ a, weighted s (U*P.projection a-P.projection (σ a)*U)≤η) :
    familyNorm (fun r : RecordType pre =>
      stack (fun a => U*P.projection a-P.projection (σ a)*U)*recordingWord pre r*s.xi)≤
      Real.sqrt 3*η+2*m*Real.sqrt 3*η := by
  simp only [recordingWord,←List.ofFn_eq_map]
  apply recorded_column_bound (fun i => (pre i).projection)
    (fun i => by simpa only [(pre i).selfadjoint,(pre i).idempotent] using (pre i).complete)
    (fun i => by simpa only [(pre i).selfadjoint,(pre i).idempotent] using (pre i).complete)
    (fun i => by rcases (pre i).arity with h | h <;> omega)
    s.xi _ η (Real.sqrt 3*η) 2 hη (by norm_num) hstate
  · exact intertwining_column_norm P U hU σ
  · change familyNorm (fun a => (U*P.projection a-P.projection (σ a)*U)*s.xi)≤_
    exact intertwining_column_error s P U σ η hη h

/-- Telescoping in the family norm retains all branches together. -/
 theorem path_error_sum {ι : Type*} [Fintype ι] {d : ℕ}
    (A : ℕ → ι → Mat d) (e : ℕ → ℝ)
    (hstep : ∀ k, familyNorm (fun a => A (k+1) a-A k a)≤e k) :
    ∀ n, familyNorm (fun a => A n a-A 0 a)≤∑ k∈Finset.range n, e k := by
  intro n
  induction n with
  | zero => simp [familyNorm,stack,hs,hsNorm,hsSquared]
  | succ n ih =>
    have he : (fun a => A (n+1) a-A 0 a)=
        (fun a => (A (n+1) a-A n a)+(A n a-A 0 a)) := by funext a; abel
    rw [he,Finset.sum_range_succ]
    exact (familyNorm_add _ _).trans (by linarith [hstep n])

end
end E2.Recording

