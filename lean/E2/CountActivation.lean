import E2.CountVariation
import E2.CountHolevo

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 400000

 theorem family_square_variation {ι : Type*} [Fintype ι] {d : ℕ} (A B : ι → Mat d)
    (hA : Recording.familyNorm A≤1) (hB : Recording.familyNorm B≤1) :
    |Recording.familyNorm A^2-Recording.familyNorm B^2|≤2*Recording.familyNorm (fun a => A a-B a) := by
  have h1 : Recording.familyNorm A≤Recording.familyNorm (fun a => A a-B a)+Recording.familyNorm B := by
    have he : (fun a => (A a-B a)+B a)=A := by funext a; abel
    simpa only [he] using Recording.familyNorm_add (fun a => A a-B a) B
  have h2 : Recording.familyNorm B≤Recording.familyNorm (fun a => A a-B a)+Recording.familyNorm A := by
    have he : (fun a => -(A a-B a)+A a)=B := by funext a; abel
    simpa only [he, record_family_neg] using Recording.familyNorm_add (fun a => -(A a-B a)) A
  have hab : |Recording.familyNorm A-Recording.familyNorm B|≤Recording.familyNorm (fun a => A a-B a) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (Recording.familyNorm_nonneg _) (Recording.familyNorm_nonneg _))]
  nlinarith [Recording.familyNorm_nonneg A, Recording.familyNorm_nonneg B, Recording.familyNorm_nonneg (fun a => A a-B a)]

/-- Disturbance by the entire suffix, summed over every suffix record. -/
 theorem head_mass_transport {d n : ℕ} (s : State d) (η : ℝ) (p : Fin n → Measurement d)
    (F : Mat d) (hF : Domain.projection.Holds F) (hη : 0≤η)
    (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi)≤η) :
    |(∑ a : RecordType p, hs (F*reverseWord p a*s.xi)^2)-hs (F*s.xi)^2|≤2*n*Real.sqrt 3*η := by
  let A (a : RecordType p) := F*reverseWord p a*s.xi
  let B (a : RecordType p) := F*s.xi*reverseWord p a
  have hbase : Recording.familyNorm (fun a : RecordType p => reverseWord p a*s.xi)=1 := by
    apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [Recording.familyNorm_sq]
    simpa only [recordMass, one_pow] using (record_normalization d n s p).2
  have hA : Recording.familyNorm A≤1 := by
    calc
      _ = Recording.familyNorm (fun a : RecordType p => F*(reverseWord p a*s.xi)) := by
        simp only [A, Matrix.mul_assoc]
      _ ≤ ‖F‖*Recording.familyNorm (fun a : RecordType p => reverseWord p a*s.xi) :=
        Recording.familyNorm_rectangular_mul F _
      _ ≤ 1 := by rw [hbase, mul_one]; exact projection_norm_le hF
  have hB : Recording.familyNorm B=hs (F*s.xi) := by
    apply (sq_eq_sq₀ (Recording.familyNorm_nonneg _) (hsNorm_nonneg _)).mp
    rw [Recording.familyNorm_sq, Recording.parseval_right _ (reverse_record_cocomplete p)]
  have hcomm : Recording.familyNorm (fun a : RecordType p => comm (reverseWord p a) s.xi)≤n*(Real.sqrt 3*η) := by
    refine (reverse_record_commutator p s).trans ?_
    calc
      _ ≤ ∑ i : Fin n, Real.sqrt 3*η := Finset.sum_le_sum (fun i _ =>
        Recording.single_commutator_bound _ s.xi η hη
          (by rcases (p i).arity with h | h <;> omega) (hstate i))
      _ = _ := by simp
  have hdiff : Recording.familyNorm (fun a => A a-B a)≤n*(Real.sqrt 3*η) := by
    have he : (fun a => A a-B a)=(fun a : RecordType p => F*comm (reverseWord p a) s.xi) := by
      funext a
      dsimp [A,B,comm,Companion.Analytic.comm]
      noncomm_ring
    rw [he]
    exact (Recording.familyNorm_rectangular_mul F _).trans
      ((mul_le_mul (projection_norm_le hF) hcomm (Recording.familyNorm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have h := family_square_variation A B hA (by rw [hB]; exact projection_weighted_le_one s F hF)
  rw [hB, Recording.familyNorm_sq] at h
  exact h.trans (by nlinarith)

 theorem marginal_mass_head {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d) (b : Fin (p 0).outcomes) :
    marginalMass s p 0 b = ∑ a : RecordType (fun j => p j.succ), hs ((p 0).projection b*reverseWord (fun j => p j.succ) a*s.xi)^2 := by
  rw [marginalMass, Recording.sum_records_cons]
  simp only [Fin.cons_zero, recordMass, reverse_word_cons]
  simp

 theorem marginal_mass_succ {d n : ℕ} (s : State d) (p : Fin (n+1) → Measurement d)
    (j : Fin n) (b : Fin (p j.succ).outcomes) :
    marginalMass s p j.succ b=marginalMass s (fun k => p k.succ) j b := by
  rw [marginalMass, Recording.sum_records_cons, Finset.sum_comm]
  simp only [Fin.cons_succ, recordMass, reverse_word_cons]
  have hP : (∑ b, ((p 0).projection b).conjTranspose*(p 0).projection b)=1 := by
    simpa only [(p 0).selfadjoint, (p 0).idempotent] using (p 0).complete
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a j=b
  · simp only [h, ite_true, marginalMass, recordMass]
    simpa only [Matrix.mul_assoc] using Recording.parseval_left (p 0).projection hP
      (reverseWord (fun k => p k.succ) a*s.xi)
  · simp [h]

 theorem marginal_mass_transport {d m : ℕ} (s : State d) (η : ℝ) (p : Fin m → Measurement d)
    (hη : 0≤η) (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi)≤η) :
    ∀ (i : Fin m) (b : Fin (p i).outcomes), |marginalMass s p i b-expectation s ((p i).projection b)|≤2*m*Real.sqrt 3*η := by
  induction m with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro b
      rw [marginal_mass_head, projection_expectation_eq s _ ⟨(p 0).selfadjoint b, (p 0).idempotent b⟩]
      have h := head_mass_transport s η (fun j => p j.succ) ((p 0).projection b)
        ⟨(p 0).selfadjoint b, (p 0).idempotent b⟩ hη (fun j => hstate j.succ)
      refine h.trans ?_
      push_cast
      nlinarith [mul_nonneg (Real.sqrt_nonneg 3) hη]
    · intro b
      rw [marginal_mass_succ]
      have h := ih (fun k => p k.succ) (fun k => hstate k.succ) j b
      refine h.trans ?_
      push_cast
      nlinarith [mul_nonneg (Real.sqrt_nonneg 3) hη]

 theorem recorded_active_complement {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) :
    recordedActive s p i=1-marginalMass s p i ((p i).index 0) := by
  have h : marginalMass s p i ((p i).index 0)+recordedActive s p i=1 := by
    rw [marginalMass, recordedActive, ←Finset.sum_add_distrib]
    have he (a : RecordType p) :
        (if a i=(p i).index 0 then recordMass s p a else 0)+
          (if a i=(p i).index 0 then 0 else recordMass s p a)=recordMass s p a := by split_ifs <;> simp
    simp_rw [he]
    exact (record_normalization d m s p).2
  linarith

 theorem active_probability_transport : Turn9.ActiveProbabilityTransport := by
  refine ⟨4, by norm_num, ?_⟩
  intro d m s η p hη hstate i hi
  have he : expectation s (p i).active=1-expectation s ((p i).projection ((p i).index 0)) := by
    simp only [Measurement.active, hi, ite_true, expectation, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_sub, Complex.sub_re, s.normalized, Complex.one_re]
  rw [recorded_active_complement, he]
  have h := marginal_mass_transport s η p hη hstate i ((p i).index 0)
  have hab : |1-marginalMass s p i ((p i).index 0)-
      (1-expectation s ((p i).projection ((p i).index 0)))| =
      |marginalMass s p i ((p i).index 0)-expectation s ((p i).projection ((p i).index 0))| := by
    have he : 1-marginalMass s p i ((p i).index 0)-(1-expectation s ((p i).projection ((p i).index 0))) =
      -(marginalMass s p i ((p i).index 0)-expectation s ((p i).projection ((p i).index 0))) := by ring
    rw [he, abs_neg]
  rw [hab]
  refine h.trans ?_
  have hroot : Real.sqrt 3≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3), Real.sqrt_nonneg 3]
  nlinarith [mul_le_mul_of_nonneg_left hroot (show (0:ℝ)≤2*m*η by positivity)]

end
end E2

