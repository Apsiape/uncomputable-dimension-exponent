import E2.AffineRepair

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

theorem reflection_unitary {d : ℕ} (X : Mat d) (hX : Domain.reflection.Holds X) :
    Domain.unitary.Holds X := by exact ⟨by rw [hX.1,hX.2],by rw [hX.1,hX.2]⟩

theorem translate_one {d : ℕ} (T : Mat d) (hT : Domain.unitary.Holds T) (i : ℕ) :
    translate T (1:Mat d) i=1 := by
  simpa only [translate_eq_conjugate,Matrix.mul_one] using (unitary_power hT i).2

theorem translate_mul {d : ℕ} (T A B : Mat d) (hT : Domain.unitary.Holds T) (i : ℕ) :
    translate T (A*B) i=translate T A i*translate T B i := by
  simpa only [translate_eq_conjugate] using (unitary_conjugation_mul (T^i) A B (unitary_power hT i)).symm

theorem translate_add {d : ℕ} (T A : Mat d) (i j : ℕ) :
    translate T (translate T A i) j=translate T A (i+j) := by
  induction j with
  | zero => simp [translate]
  | succ j ih => rw [translate_succ,ih,Nat.add_succ,translate_succ]

theorem translate_reflection {d : ℕ} (T X : Mat d) (hT : Domain.unitary.Holds T)
    (hX : Domain.reflection.Holds X) (i : ℕ) : Domain.reflection.Holds (translate T X i) := by
  refine ⟨(translate_hermitian T X hX.1 i).eq,?_⟩
  rw [←translate_mul T X X hT i,hX.2,translate_one T hT i]

theorem translated_state_commutator {d : ℕ} (s : State d) (δ : ℝ) (T A : Mat d)
    (hδ : 0≤δ) (hT : Domain.unitary.Holds T) (hnA : ‖A‖≤1)
    (hσT : hs (comm T s.xi)≤δ) (hσA : hs (comm A s.xi)≤δ) (i : ℕ) :
    hs (comm (translate T A i) s.xi)≤(2*(i:ℝ)+1)*δ := by
  have hd := state_dimension_pos s
  let xs := List.replicate i T++[A]++List.replicate i T.conjTranspose
  have hcases (a : Mat d) (ha : a∈xs) : a=T ∨ a=A ∨ a=T.conjTranspose := by
    simp only [xs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with (h|h) | h
    · exact Or.inl (List.mem_replicate.mp h).2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_replicate.mp h).2)
  have hn : ∀ a∈xs,‖a‖≤1 := by
    intro a ha
    rcases hcases a ha with rfl | rfl | rfl
    · exact (unitary_norm hd hT).le
    · exact hnA
    · exact (unitary_norm hd (unitary_adjoint hT)).le
  have hc : ∀ a∈xs,hs (comm a s.xi)≤δ := by
    intro a ha
    rcases hcases a ha with rfl | rfl | rfl
    · exact hσT
    · exact hσA
    · rw [unitary_adjoint_state_commutator s T hT]; exact hσT
  have h := word_state_commutator s hd δ hδ xs hn hc
  have hp : xs.prod=translate T A i := by simp [xs,List.prod_append,List.prod_replicate,translate,Matrix.mul_assoc]
  have hl : xs.length=2*i+1 := by simp only [xs,List.length_append,List.length_replicate,List.length_singleton]; omega
  rw [hp,hl] at h
  push_cast at h
  exact h

theorem raw_clock_state_commutators {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hc : ClockApprox s δ c) (j : ℕ) :
    hs (comm (rawDigit c j) s.xi)≤(2*(j:ℝ)+1)*δ ∧
    hs (comm (rawFlip c j) s.xi)≤(2*(j:ℝ)+1)*δ := by
  have hT := hc.1.2.2.1
  have hσT := hc.2.2 c.T (by simp [ClockData.variables])
  constructor
  · exact translated_state_commutator s δ c.T c.P hδ hT (projection_norm_le hc.1.2.1)
      hσT (hc.2.2 c.P (by simp [ClockData.variables])) j
  · exact translated_state_commutator s δ c.T c.X hδ hT
      (unitary_norm (state_dimension_pos s) (reflection_unitary c.X hc.1.2.2.2)).le
      hσT (hc.2.2 c.X (by simp [ClockData.variables])) j

theorem raw_own_bit_flip {d : ℕ} (s : State d) (δ : ℝ) (c : ClockData d)
    (hδ : 0≤δ) (hc : ClockApprox s δ c) (j : ℕ) :
    weighted s (rawFlip c j*rawDigit c j*rawFlip c j-(1-rawDigit c j))≤(2*(j:ℝ)+1)*δ := by
  have hP := hc.1.2.1
  have hT := hc.1.2.2.1
  have hX := hc.1.2.2.2
  have hXu := reflection_unitary c.X hX
  let E := c.X*c.P*c.X-(1-c.P)
  have hE : weighted s E≤δ := hc.2.1 _ (by simp [ClockData.defects,E])
  have hnXPX : ‖c.X*c.P*c.X‖≤1 := by
    have h := translate_norm s c.X c.P hXu 1
    simpa only [translate,pow_one,hX.1] using h.trans (projection_norm_le hP)
  have hnE : ‖E‖≤2 := (norm_sub_le _ _).trans (by linarith [projection_norm_le (projection_complement hP)])
  have ht := translate_weighted s c.T E hT δ hδ (hc.2.2 c.T (by simp [ClockData.variables])) j
  have he : translate c.T E j=rawFlip c j*rawDigit c j*rawFlip c j-(1-rawDigit c j) := by
    simp only [E,translate_sub,translate_mul c.T _ _ hT j,translate_one c.T hT j]
    rfl
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_right hnE (mul_nonneg (Nat.cast_nonneg j) hδ)
  nlinarith only [ht,hE,hm]

end
end E2

#print axioms E2.reflection_unitary
#print axioms E2.translate_one
#print axioms E2.translate_mul
#print axioms E2.translate_add
#print axioms E2.translate_reflection
#print axioms E2.translated_state_commutator
#print axioms E2.raw_clock_state_commutators
#print axioms E2.raw_own_bit_flip
