import E2.ExactProgramIteration
import E2.ExactIncrementModel

namespace E2.ExactForcing
noncomputable section
open ExactClock
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem prefix_projection (P : ℕ → A) (hp : ∀ j, IsStarProjection (P j))
    (hpp : ∀ i j, Commute (P i) (P j)) (j M : ℕ) (b : ℕ → Bool) :
    IsStarProjection (clockPrefix P j M b) := by
  induction M generalizing j b with
  | zero => rw [prefix_zero]; exact .one A
  | succ M ih =>
    rw [prefix_succ]
    have hc : Commute (P j) (clockPrefix P (j+1) M (dropBits b 1)) :=
      prefix_commute P (j+1) M _ _ (fun k => hpp j _)
    cases hb : b 0
    · simp only [hb,Bool.false_eq_true,ite_false]
      exact (hp j).one_sub.mul (ih _ _) ((Commute.one_left _).sub_left hc)
    · simp only [hb,ite_true]
      exact (hp j).mul (ih _ _) hc

theorem prefix_map (f : A →⋆ₐ[ℂ] A) (P : ℕ → A) (j M : ℕ) (b : ℕ → Bool) :
    f (clockPrefix P j M b)=clockPrefix (fun k => f (P k)) j M b := by
  simp only [clockPrefix,cylinder,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  split_ifs <;> simp

theorem prefix_absorb (P : ℕ → A) (hp : ∀ j, IsIdempotentElem (P j))
    (hpp : ∀ i j, Commute (P i) (P j)) (j M : ℕ) (b : ℕ → Bool) (i : ℕ) (hi : i<M) :
    P (j+i)*clockPrefix P j M b=if b i then clockPrefix P j M b else 0 := by
  induction M generalizing j b i with
  | zero => omega
  | succ M ih =>
    rw [prefix_succ]
    cases i with
    | zero =>
      simp only [Nat.add_zero]
      cases hb : b 0 <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true]
      · rw [←mul_assoc,(hp j).mul_one_sub_self,zero_mul]
      · rw [←mul_assoc,(hp j).eq]
    | succ i =>
      have hc : Commute (P (j+(i+1))) (if b 0 then P j else 1-P j) := by
        split_ifs
        · exact hpp _ _
        · exact (Commute.one_right _).sub_right (hpp _ _)
      rw [←mul_assoc,hc.eq,mul_assoc]
      have he : j+(i+1)=(j+1)+i := by omega
      rw [he,ih (j+1) (dropBits b 1) i (by omega)]
      change (if b 0 then P j else 1-P j)*(if b (i+1) then _ else 0)=_
      split_ifs <;> simp

theorem prefix_distinct_zero (P : ℕ → A) (hp : ∀ j, IsIdempotentElem (P j))
    (hpp : ∀ i j, Commute (P i) (P j)) (j M : ℕ) (b c : ℕ → Bool)
    (i : ℕ) (hi : i<M) (hbc : b i≠c i) :
    clockPrefix P j M b*clockPrefix P j M c=0 := by
  have hb := prefix_absorb P hp hpp j M b i hi
  have hc := prefix_absorb P hp hpp j M c i hi
  have hcomm : Commute (P (j+i)) (clockPrefix P j M b) :=
    prefix_commute P j M b _ (fun k => (hpp _ _).eq)
  cases hbi : b i <;> cases hci : c i <;> simp only [hbi,hci,Bool.false_eq_true,ite_false,ite_true] at hb hc hbc
  · exact False.elim (hbc rfl)
  · rw [←hc,←mul_assoc,←hcomm.eq,hb,zero_mul]
  · rw [←hb,hcomm.eq,mul_assoc,hc,mul_zero]
  · exact False.elim (hbc rfl)

theorem nonzero_prefix_bit (b : ℕ → Bool) (M : ℕ) (hb : binaryPrefix b M≠0) :
    ∃ i, i<M ∧ b i=true := by
  by_contra h
  push Not at h
  apply hb
  simp only [binaryPrefix]
  apply Finset.sum_eq_zero
  intro i hi
  have hfalse : b i=false := by
    cases hb : b i
    · rfl
    · exact False.elim (h i (Finset.mem_range.mp hi) hb)
  rw [hfalse]
  rfl

theorem decrement_not_zero (M l : ℕ) (hl : 0<l) (hlt : l<2^M) :
    binaryPrefix (addBits (l*(2^M-1)) (fun _ => false)) M≠0 := by
  rw [binaryPrefix_addBits]
  simp only [binaryPrefix,Bool.false_eq_true,ite_false,Finset.sum_const_zero,Nat.add_zero]
  intro hz
  have hp : 0<2^M := by positivity
  have he : l*(2^M-1)+l=l*2^M := by nlinarith [Nat.sub_add_cancel (show 1≤2^M by omega)]
  have hm := congrArg (fun n => n%2^M) he
  rw [Nat.add_mod,hz,Nat.mod_eq_of_lt hlt,Nat.zero_add,Nat.mod_eq_of_lt hlt,Nat.mul_mod_left] at hm
  omega

theorem remove_factor (f : A →⋆ₐ[ℂ] A) (z p q : A)
    (hz : f z=z) (hp : f p=1-p) (hq : f q=q) (b : Bool)
    (h : z*(if b then p else 1-p)*q=0) : z*q=0 := by
  have hf := congrArg f h
  simp only [map_mul,map_zero,map_sub,map_one,hz,hp,hq] at hf
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,sub_sub_cancel] at h hf
  all_goals calc
    z*q = z*p*q+z*(1-p)*q := by noncomm_ring
    _ = 0 := by simp_all

end
end E2.ExactForcing
