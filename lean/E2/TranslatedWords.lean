import E2.Carry

namespace E2
noncomputable section
open Companion.Analytic
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

theorem weighted_unitary_adjoint_commutator {d : ℕ} (s : State d) (U Y : Mat d)
    (hU : Domain.unitary.Holds U) (hnY : ‖Y‖≤1) :
    weighted s (comm U.conjTranspose Y)≤weighted s (comm U Y)+2*hs (comm U s.xi) := by
  have hnU : ‖U‖≤1 := (unitary_norm (state_dimension_pos s) hU).le
  have hnUa : ‖U.conjTranspose‖=1 := unitary_norm (state_dimension_pos s) (unitary_adjoint hU)
  have hnE : ‖comm U Y‖≤2 := norm_comm_contractions U Y hnU hnY
  have he : comm U.conjTranspose Y= -(U.conjTranspose*comm U Y*U.conjTranspose) := by
    have h : U.conjTranspose*comm U Y*U.conjTranspose=Y*U.conjTranspose-U.conjTranspose*Y := by
      calc
        _=(U.conjTranspose*U)*Y*U.conjTranspose-U.conjTranspose*Y*(U*U.conjTranspose) := by
          simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
        _=_ := by rw [hU.1,hU.2]; simp
    rw [h]
    simp only [comm,Companion.Analytic.comm]
    abel
  rw [he]
  have hneg : weighted s (-(U.conjTranspose*comm U Y*U.conjTranspose))=
      weighted s (U.conjTranspose*comm U Y*U.conjTranspose) := by
    simp only [weighted,Matrix.neg_mul,hs_neg_matrix]
  rw [hneg,Matrix.mul_assoc]
  calc
    _≤‖U.conjTranspose‖*weighted s (comm U Y*U.conjTranspose) := weighted_left _ _ _
    _=weighted s (comm U Y*U.conjTranspose) := by rw [hnUa,one_mul]
    _≤‖U.conjTranspose‖*weighted s (comm U Y)+‖comm U Y‖*hs (comm U.conjTranspose s.xi) := weighted_right _ _ _
    _≤weighted s (comm U Y)+2*hs (comm U s.xi) := by
      rw [hnUa,one_mul,unitary_adjoint_state_commutator s U hU]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hnE (hsNorm_nonneg _))

/-- Different compulsory clocks, and conditional versus fuel/time, are routed
through these raw words. Adjoint letters add only state transport costs. -/
theorem translated_word_commutator {d : ℕ} (s : State d) (δ : ℝ) (T U Y Z : Mat d)
    (hδ : 0≤δ) (hT : Domain.unitary.Holds T) (hU : Domain.unitary.Holds U)
    (hnY : ‖Y‖≤1) (hnZ : ‖Z‖≤1)
    (hσT : hs (comm T s.xi)≤δ) (hσU : hs (comm U s.xi)≤δ)
    (hσY : hs (comm Y s.xi)≤δ) (hσZ : hs (comm Z s.xi)≤δ)
    (hTU : weighted s (comm T U)≤δ) (hTZ : weighted s (comm T Z)≤δ)
    (hYU : weighted s (comm Y U)≤δ) (hYZ : weighted s (comm Y Z)≤δ) (i j : ℕ) :
    weighted s (comm (translate T Y i) (translate U Z j))≤
      5*(2*(i:ℝ)+1)*(2*(j:ℝ)+1)*(2*i+2*j+3)*δ := by
  have hd := state_dimension_pos s
  have hnT : ‖T‖≤1 := (unitary_norm hd hT).le
  have hnU : ‖U‖≤1 := (unitary_norm hd hU).le
  have hnTa : ‖T.conjTranspose‖≤1 := (unitary_norm hd (unitary_adjoint hT)).le
  have hnUa : ‖U.conjTranspose‖≤1 := (unitary_norm hd (unitary_adjoint hU)).le
  have hTaU : weighted s (comm T.conjTranspose U)≤3*δ := by
    have h := weighted_unitary_adjoint_commutator s T U hT hnU
    linarith
  have hTaZ : weighted s (comm T.conjTranspose Z)≤3*δ := by
    have h := weighted_unitary_adjoint_commutator s T Z hT hnZ
    linarith
  have hTUa : weighted s (comm T U.conjTranspose)≤3*δ := by
    have h := weighted_unitary_adjoint_commutator s U T hU hnT
    rw [weighted_comm_symm s U.conjTranspose T,weighted_comm_symm s U T] at h
    linarith
  have hYUa : weighted s (comm Y U.conjTranspose)≤3*δ := by
    have h := weighted_unitary_adjoint_commutator s U Y hU hnY
    rw [weighted_comm_symm s U.conjTranspose Y,weighted_comm_symm s U Y] at h
    linarith
  have hTaUa : weighted s (comm T.conjTranspose U.conjTranspose)≤5*δ := by
    have h := weighted_unitary_adjoint_commutator s U T.conjTranspose hU hnTa
    rw [weighted_comm_symm s U.conjTranspose T.conjTranspose,weighted_comm_symm s U T.conjTranspose] at h
    linarith
  let xs := List.replicate i T++[Y]++List.replicate i T.conjTranspose
  let ys := List.replicate j U++[Z]++List.replicate j U.conjTranspose
  have hx (A : Mat d) (hA : A∈xs) : A=T ∨ A=Y ∨ A=T.conjTranspose := by
    simp only [xs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with (h|h)|h
    · exact Or.inl (List.mem_replicate.mp h).2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_replicate.mp h).2)
  have hy (A : Mat d) (hA : A∈ys) : A=U ∨ A=Z ∨ A=U.conjTranspose := by
    simp only [ys,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hA
    rcases hA with (h|h)|h
    · exact Or.inl (List.mem_replicate.mp h).2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (List.mem_replicate.mp h).2)
  have hnx : ∀ A∈xs, ‖A‖≤1 := by
    intro A hA
    rcases hx A hA with rfl | rfl | rfl <;> assumption
  have hny : ∀ A∈ys, ‖A‖≤1 := by
    intro A hA
    rcases hy A hA with rfl | rfl | rfl <;> assumption
  have hsx : ∀ A∈xs, hs (comm A s.xi)≤5*δ := by
    intro A hA
    rcases hx A hA with rfl | rfl | rfl
    · linarith
    · linarith
    · rw [unitary_adjoint_state_commutator s T hT]; linarith
  have hsy : ∀ A∈ys, hs (comm A s.xi)≤5*δ := by
    intro A hA
    rcases hy A hA with rfl | rfl | rfl
    · linarith
    · linarith
    · rw [unitary_adjoint_state_commutator s U hU]; linarith
  have hb : ∀ A∈xs, ∀ B∈ys, weighted s (comm A B)≤5*δ := by
    intro A hA B hB
    rcases hx A hA with rfl | rfl | rfl <;>
      rcases hy B hB with rfl | rfl | rfl <;> linarith
  have h := raw_word_interchange s hd (5*δ) (by positivity) xs ys hnx hsx hny hsy hb
  have hp : xs.prod=translate T Y i ∧ ys.prod=translate U Z j := by
    simp only [xs,ys,List.prod_append,List.prod_replicate,List.prod_singleton,translate,Matrix.mul_assoc,and_self]
  rw [hp.1,hp.2] at h
  have hlen : xs.length=2*i+1 ∧ ys.length=2*j+1 := by
    simp only [xs,ys,List.length_append,List.length_replicate,List.length_singleton]; omega
  rw [hlen.1,hlen.2] at h
  push_cast at h
  convert h using 1 <;> ring

end
end E2
