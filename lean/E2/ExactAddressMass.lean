import E2.ExactHaltingCorner

namespace E2.ExactForcing
noncomputable section
open ExactClock
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem pair_product (f : ℕ → A) (n : ℕ) :
    ((List.range n).map (fun j => f (2*j)*f (2*j+1))).prod=
      ((List.range (2*n)).map f).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ,ih,show 2*(n+1)=(2*n+1)+1 by omega,
      List.prod_range_succ,List.prod_range_succ,mul_assoc]

def addressBits (e j : ℕ) : Bool := decide (j=2*e)

theorem address_prefix {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e : ℕ) :
    addressCylinder m e=clockPrefix (ctranslate (sourceValue m 2) (sourceValue m 1))
      0 (2*e+2) (addressBits e) := by
  let v := sourceValue m
  let P := ctranslate (v 2) (v 1)
  have ht : star (v 2)*v 2=1 ∧ v 2*star (v 2)=1 := (sourceClockModel m 0).domains 2
  have hblocks : ((List.range e).map (fun j =>
      ctranslate (v 2) ((1-v 1)*(1-ctranslate (v 2) (v 1) 1)) (2*j))).prod=
      ((List.range (2*e)).map (fun j => 1-P j)).prod := by
    rw [←pair_product]
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [shift_mul _ _ _ ht,shift_sub,shift_sub,shift_one _ ht,shift_shift]
    simp only [P,Nat.add_comm 1]
  have hb : ctranslate (v 2) (v 1*(1-ctranslate (v 2) (v 1) 1)) (2*e)=P (2*e)*(1-P (2*e+1)) := by
    rw [shift_mul _ _ _ ht,shift_sub,shift_one _ ht,shift_shift]
    simp only [P,Nat.add_comm 1]
  change ((List.range e).map _).prod*ctranslate (v 2) (v 1*(1-ctranslate (v 2) (v 1) 1)) (2*e)=_
  rw [hblocks,hb,prefix_range,show 2*e+2=(2*e+1)+1 by omega,
    List.prod_range_succ,List.prod_range_succ]
  simp only [addressBits,decide_true,ite_true,show ¬2*e+1=2*e by omega,decide_false,Bool.false_eq_true,ite_false]
  rw [mul_assoc]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  simp [P,v,addressBits,show j≠2*e by have := List.mem_range.mp hj; omega]

theorem address_projection {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e : ℕ) :
    IsStarProjection (addressCylinder m e) := by
  rw [address_prefix]
  exact prefix_projection _ (model_digit_projection (sourceClockModel m 0))
    (model_digit_commute (sourceClockModel m 0)) 0 (2*e+2) _

theorem address_orthogonal_lt {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (e f : ℕ) (hef : e<f) : addressCylinder m e*addressCylinder m f=0 := by
  let P := ctranslate (sourceValue m 2) (sourceValue m 1)
  have hp (j : ℕ) := (model_digit_projection (sourceClockModel m 0) j).isIdempotentElem
  have hpp (i j : ℕ) := model_digit_commute (sourceClockModel m 0) i j
  have he := prefix_absorb P hp hpp 0 (2*e+2) (addressBits e) (2*e) (by omega)
  have hf := prefix_absorb P hp hpp 0 (2*f+2) (addressBits f) (2*e) (by omega)
  rw [←address_prefix] at he hf
  simp only [addressBits,Nat.zero_add,decide_true,ite_true] at he
  simp only [addressBits,Nat.zero_add,show ¬2*e=2*f by omega,decide_false,Bool.false_eq_true,ite_false] at hf
  have hc : Commute (P (2*e)) (addressCylinder m e) := by
    rw [address_prefix]
    exact prefix_commute P 0 _ _ _ (fun k => (hpp _ _).eq)
  rw [←he,hc.eq,mul_assoc,hf,mul_zero]

theorem address_orthogonal {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (e f : ℕ) (hef : e≠f) : addressCylinder m e*addressCylinder m f=0 := by
  rcases lt_or_gt_of_ne hef with h | h
  · exact address_orthogonal_lt m e f h
  · have hh := congrArg star (address_orthogonal_lt m f e h)
    simpa only [star_mul,(address_projection m e).isSelfAdjoint.star_eq,
      (address_projection m f).isSelfAdjoint.star_eq,star_zero] using hh

theorem address_mass {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e : ℕ) :
    m.state.toLinearMap (addressCylinder m e)=(4:ℂ)^(-(e+1:ℤ)) := by
  rw [address_prefix]
  have hf := (model_digits (sourceClockModel m 0)).2.2.2.2.2 (2*e+2) (fun i => addressBits e i.val)
  change m.state.toLinearMap (cylinder _ (2*e+2) _)=(4:ℂ)^(-(e+1:ℤ))
  simp only [Nat.zero_add]
  calc
    _=(2:ℂ)^(-((2*e+2:ℕ):ℤ)) := by convert hf using 1 <;> rfl
    _=_ := by
      rw [show (-(e+1:ℤ)) = -((e+1:ℕ):ℤ) by omega]
      simp only [zpow_neg,zpow_natCast]
      congr 1
      rw [show 2*e+2=2*(e+1) by omega,pow_mul]
      norm_num

end
end E2.ExactForcing
