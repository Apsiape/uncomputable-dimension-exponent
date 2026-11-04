import E2.CountSuffix

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

 theorem normalized_family_variation {ι : Type*} [Fintype ι] {d : ℕ}
    (A B : ι → Mat d) (hA : (∑ a, hs (A a)^2)=1) (hB : (∑ a, hs (B a)^2)=1) :
    (∑ a, |hs (A a)^2-hs (B a)^2|) ≤ 2*Recording.familyNorm (fun a => A a-B a) := by
  have hpoint (i : ι) : |hs (A i)^2-hs (B i)^2| ≤
      (hs (A i)+hs (B i))*hs (A i-B i) := by
    have h1 : hs (A i)≤hs (A i-B i)+hs (B i) := by
      simpa only [sub_add_cancel] using hsNorm_add_le (A i-B i) (B i)
    have h2 : hs (B i)≤hs (A i-B i)+hs (A i) := by
      have h := hsNorm_add_le (-(A i-B i)) (A i)
      have he : -(A i-B i)+A i=B i := by abel
      simpa only [he, hs_neg_matrix] using h
    have hab : |hs (A i)-hs (B i)|≤hs (A i-B i) := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _))]
    nlinarith [hsNorm_nonneg (A i), hsNorm_nonneg (B i)]
  have hsq : (∑ i, (hs (A i)+hs (B i))^2)≤4 := by
    calc
      _ ≤ ∑ i, (2*hs (A i)^2+2*hs (B i)^2) :=
        Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (hs (A i)-hs (B i))])
      _ = 4 := by rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum, hA, hB]; norm_num
  calc
    _ ≤ ∑ i, (hs (A i)+hs (B i))*hs (A i-B i) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ Real.sqrt (∑ i, (hs (A i)+hs (B i))^2) * Real.sqrt (∑ i, hs (A i-B i)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ 2*Recording.familyNorm (fun i => A i-B i) := by
      rw [Recording.familyNorm_eq_sqrt]
      gcongr
      exact (Real.sqrt_le_sqrt hsq).trans_eq (by norm_num)

 def recordSwapEquiv {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m) :
    Equiv.Perm (RecordType p) := Equiv.piCongrRight
      (Function.update (fun j => Equiv.refl (Fin (p j).outcomes)) i (p i).swap)

 theorem recordSwapEquiv_apply {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m) (a : RecordType p) :
    recordSwapEquiv p i a=swapRecord p i a := by
  funext j
  by_cases h : j=i
  · subst j
    simp [recordSwapEquiv, swapRecord]
  · simp [recordSwapEquiv, swapRecord, h]

 theorem suffix_swap_bound : Turn9.SuffixSwapBound := by
  obtain ⟨C, hC, hvec⟩ := suffix_swap_vector
  refine ⟨C, hC, ?_⟩
  intro d m s η p u hη hrel i
  let q := suffix p i.val
  let zero : Fin (m-i.val) := ⟨0, by omega⟩
  let A (a : RecordType q) := reverseWord q (swapRecord q zero a)*s.xi
  let B (a : RecordType q) := u i*(reverseWord q a*s.xi)*(u i).conjTranspose
  have hU := hrel.1 i
  have hB (a : RecordType q) : hs (B a)=hs (reverseWord q a*s.xi) := by
    dsimp [B]
    exact (hsNorm_unitary_right (u i).conjTranspose (u i*(reverseWord q a*s.xi))
      (by simpa using hU.1)).trans (hsNorm_unitary_left (u i) (reverseWord q a*s.xi) hU.1)
  have hnormA : (∑ a : RecordType q, hs (A a)^2)=1 := by
    calc
      _ = ∑ a : RecordType q, recordMass s q (recordSwapEquiv q zero a) := by simp only [A, recordSwapEquiv_apply, recordMass]
      _ = ∑ a : RecordType q, recordMass s q a := Fintype.sum_equiv (recordSwapEquiv q zero) _ _ (fun _ => rfl)
      _ = 1 := (record_normalization d (m-i.val) s q).2
  have hnormB : (∑ a : RecordType q, hs (B a)^2)=1 := by
    simp_rw [hB]
    exact (record_normalization d (m-i.val) s q).2
  have h := normalized_family_variation A B hnormA hnormB
  have hv := hvec d m s η p u hη hrel i
  have he : (∑ a : RecordType q, |hs (A a)^2-hs (B a)^2|) = 2*swapVariation s q zero := by
    simp only [A, hB, recordMass, swapVariation]
    simp_rw [abs_sub_comm (hs (reverseWord q (swapRecord q zero _) * s.xi)^2)]
    ring
  rw [he] at h
  change Recording.familyNorm (fun a : RecordType q => A a-B a) ≤ C*m^2*η at hv
  change swapVariation s q zero ≤ _
  linarith

end
end E2

