import E2.CountPathIntertwining
import E2.Turn9.CountPathsStatements

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

 theorem record_family_neg {ι : Type*} [Fintype ι] {d : ℕ} (V : ι → Mat d) :
    Recording.familyNorm (fun a => -V a)=Recording.familyNorm V := by
  apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _)).mp
  simp only [Recording.familyNorm_sq, hs_neg_matrix]

 theorem record_family_unitary_right {ι : Type*} [Fintype ι] {d : ℕ}
    (V : ι → Mat d) (U : Mat d) (hU : Domain.unitary.Holds U) :
    Recording.familyNorm (fun a => V a*U.conjTranspose)=Recording.familyNorm V := by
  apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _)).mp
  simp only [Recording.familyNorm_sq, hsNorm_unitary_right U.conjTranspose _ (by simpa using hU.1)]

/-- Restore the original state after sliding the unitary through the word. -/
 theorem reverse_conjugation_path {d m : ℕ} (s : State d) (η : ℝ)
    (p : Fin m → Measurement d) (U : Mat d)
    (σ : ∀ i, Equiv.Perm (Fin (p i).outcomes))
    (hU : Domain.unitary.Holds U) (hη : 0≤η)
    (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi)≤η)
    (hu : hs (comm U s.xi)≤η)
    (hcross : ∀ i a, weighted s (U*(p i).projection a-(p i).projection (σ i a)*U)≤η) :
    Recording.familyNorm (fun a : RecordType p =>
      reverseWord p (fun i => σ i (a i))*s.xi-
        U*(reverseWord p a*s.xi)*U.conjTranspose) ≤ (m:ℝ)^2*Real.sqrt 3*η+η := by
  let W (a : RecordType p) := reverseWord p (fun i => σ i (a i))
  have hW : (∑ a : RecordType p, (W a).conjTranspose*W a)=1 := by
    calc
      _ = ∑ a : RecordType p, (reverseWord p a).conjTranspose*reverseWord p a :=
        Fintype.sum_equiv (Equiv.piCongrRight σ) _ _ (fun _ => rfl)
      _ = 1 := reverse_record_complete p
  have hstateNorm : Recording.familyNorm (fun a : RecordType p => W a*comm U s.xi) = hs (comm U s.xi) := by
    apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (hsNorm_nonneg _)).mp
    rw [Recording.familyNorm_sq, Recording.parseval_left _ hW]
  have he : (fun a : RecordType p => W a*s.xi-U*(reverseWord p a*s.xi)*U.conjTranspose) =
      (fun a => -(((U*reverseWord p a-W a*U)*s.xi)*U.conjTranspose+
        (W a*comm U s.xi)*U.conjTranspose)) := by
    funext a
    simp only [comm, Companion.Analytic.comm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      ←Matrix.mul_assoc U U.conjTranspose, hU.2, Matrix.mul_one]
    abel
  change Recording.familyNorm (fun a : RecordType p => W a*s.xi-U*(reverseWord p a*s.xi)*U.conjTranspose) ≤ _
  rw [he, record_family_neg]
  calc
    _ ≤ Recording.familyNorm (fun a : RecordType p => ((U*reverseWord p a-W a*U)*s.xi)*U.conjTranspose)+
        Recording.familyNorm (fun a : RecordType p => (W a*comm U s.xi)*U.conjTranspose) :=
      Recording.familyNorm_add _ _
    _ ≤ (m:ℝ)^2*Real.sqrt 3*η+η := by
      rw [record_family_unitary_right _ U hU, record_family_unitary_right _ U hU, hstateNorm]
      exact add_le_add (reverse_intertwining_path s η p U σ hU hη hstate hcross) hu

 theorem suffix_swap_vector : Turn9.SuffixSwapVector := by
  refine ⟨3, by norm_num, ?_⟩
  intro d m s η p u hη hrel i
  rcases hrel with ⟨hU, hstate, hpair, hu, hown, hlater⟩
  let q := suffix p i.val
  let zero : Fin (m-i.val) := ⟨0, by omega⟩
  have hq : q zero=p i := rfl
  let σ : ∀ j, Equiv.Perm (Fin (q j).outcomes) :=
    Function.update (fun j => Equiv.refl (Fin (q j).outcomes)) zero (q zero).swap
  have hcross : ∀ j a, weighted s (u i*(q j).projection a-(q j).projection (σ j a)*u i)≤η := by
    intro j a
    by_cases hj : j=zero
    · subst j
      simp only [σ, Function.update_self]
      change weighted s (u i*(p i).projection a-(p i).projection ((p i).swap a)*u i)≤η
      exact hown i a
    · simp only [σ, Function.update_of_ne hj, Equiv.refl_apply]
      apply hlater i ⟨i.val+j.val, by have := j.isLt; omega⟩
      change i.val < i.val+j.val
      have hz : j.val≠0 := fun h => hj (Fin.ext h)
      omega
  have hσ (a : RecordType q) : (fun j => σ j (a j))=swapRecord q zero a := by
    funext j
    by_cases hj : j=zero
    · subst j
      simp [σ, swapRecord]
    · simp [σ, swapRecord, hj]
  have h := reverse_conjugation_path s η q (u i) σ (hU i) hη
    (fun j => hstate ⟨i.val+j.val, by have := j.isLt; omega⟩) (hu i) hcross
  simp_rw [hσ] at h
  change Recording.familyNorm (fun a : RecordType q =>
    reverseWord q (swapRecord q zero a)*s.xi-u i*(reverseWord q a*s.xi)*(u i).conjTranspose) ≤ _
  refine h.trans ?_
  have hroot : Real.sqrt 3≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3), Real.sqrt_nonneg 3]
  have hnm : ((m-i.val:ℕ):ℝ)≤m := by exact_mod_cast Nat.sub_le m i.val
  have hm : 1≤(m:ℝ)^2 := by
    have hi := i.isLt
    have hmpos : 1≤m := by omega
    exact_mod_cast (show 1≤m^2 by nlinarith)
  calc
    _ ≤ (m:ℝ)^2*2*η+η := by gcongr
    _ ≤ 3*(m:ℝ)^2*η := by nlinarith [mul_le_mul_of_nonneg_right hm hη]

end
end E2



