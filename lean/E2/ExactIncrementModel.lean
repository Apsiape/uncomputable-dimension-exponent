import E2.ExactClockGuard
import E2.ExactIncrementPrefix

namespace E2.ExactClock
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

theorem shift_unitary (t v : A) (ht : star t*t=1 ∧ t*star t=1)
    (hv : star v*v=1 ∧ v*star v=1) (j : ℕ) :
    star (ctranslate t v j)*ctranslate t v j=1 ∧ ctranslate t v j*star (ctranslate t v j)=1 := by
  constructor
  · rw [shift_star,←shift_mul t (star v) v ht j,hv.1,shift_one t ht j]
  · rw [shift_star,←shift_mul t v (star v) ht j,hv.2,shift_one t ht j]

theorem model_increment (m : ExactModel clockPresentation A) (v : A)
    (hv : Domain.unitary.HoldsC v)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (guard : (v-m.value 3*((1-m.value 1)+(m.value 2*v*star (m.value 2))*m.value 1))*(1-m.value 0)=0) :
    ∀ M bits, star v*cylinder (fun j => ctranslate (m.value 2) (m.value 1) j) M bits*v=
      cylinder (fun j => ctranslate (m.value 2) (m.value 1) j) M
        (fun j => decide ((((∑ k : Fin M, if bits k then 2^k.val else 0)+2^M-1)/2^j.val)%2=1)) := by
  let t := m.value 2
  let P := ctranslate t (m.value 1)
  let X := ctranslate t (m.value 3)
  let V := ctranslate t v
  have ht : star t*t=1 ∧ t*star t=1 := m.domains 2
  have hp0 : star (m.value 1)=m.value 1 ∧ m.value 1*m.value 1=m.value 1 := m.domains 1
  have hp : ∀ j, star (P j)=P j ∧ P j*P j=P j := by
    intro j
    constructor
    · change star (ctranslate t (m.value 1) j)=_
      rw [shift_star,hp0.1]
    · change ctranslate t (m.value 1) j*ctranslate t (m.value 1) j=_
      rw [←shift_mul t _ _ ht j,hp0.2]
  have hx : ∀ j, star (X j)=X j ∧ X j*X j=1 := fun j => shift_reflection _ _ ht (m.domains 3) j
  have hv' : ∀ j, star (V j)*V j=1 ∧ V j*star (V j)=1 := shift_unitary t v ht hv
  have hd := model_digits m
  have hpp : ∀ i j, P i*P j=P j*P i := by
    intro i j
    simp only [P,t,hd.2.1]
    rw [←cfc_mul _ _ _ (digitAt_lipschitz i).continuous.continuousOn
      (digitAt_lipschitz j).continuous.continuousOn,
      ←cfc_mul _ _ _ (digitAt_lipschitz j).continuous.continuousOn (digitAt_lipschitz i).continuous.continuousOn]
    apply cfc_congr
    intro r hr
    exact mul_comm _ _
  have hrec0 : v=m.value 3*((1-m.value 1)+ctranslate t v 1*m.value 1) := by
    have h := sub_eq_zero.mp (guard_cancel m faithful _ guard)
    simpa only [ctranslate,pow_one] using h
  have hadd (a b : A) (j : ℕ) : ctranslate t (a+b) j=ctranslate t a j+ctranslate t b j := by
    simp only [ctranslate,mul_add,add_mul]
  have hrec : ∀ j, V j=X j*((1-P j)+V (j+1)*P j) := by
    intro j
    have h := congrArg (fun a => ctranslate t a j) hrec0
    simpa only [shift_mul t _ _ ht j,hadd,shift_sub,shift_one t ht j,shift_shift,
      Nat.add_comm 1 j] using h
  have hcarry : ∀ j, V (j+1)*P j=P j*V (j+1) := by
    intro j
    let d := X j*V j
    have hd' : d=(1-P j)+V (j+1)*P j := by
      have h := congrArg (fun z => X j*z) (hrec j)
      simpa only [←mul_assoc,(hx j).2,one_mul] using h
    have hdu : star d*d=1 ∧ d*star d=1 := by
      constructor
      · simp only [d,star_mul,(hx j).1,mul_assoc,←mul_assoc (X j) (X j),(hx j).2,one_mul,(hv' j).1]
      · simp only [d,star_mul,(hx j).1,mul_assoc,←mul_assoc (V j) (star (V j)),(hv' j).2,one_mul,(hx j).2]
    exact controlled_commutes (P j) (V (j+1)) d (hp j) (hv' (j+1)) hdu hd'
  intro M bits
  have h := prefix_backward P X V hp hx hv' hpp hd.2.2.2.2.1 hd.2.2.2.1 hcarry hrec M 0 (extendBits bits)
  calc
    _ = cylinder P M (fun j => addBits (2^M-1) (extendBits bits) j.val) := by
      simpa only [clockPrefix,Nat.zero_add,V,shift_zero,extendBits_apply] using h
    _ = _ := by
      congr 1
      funext j
      rw [addBits_full_prefix _ M _ j.val j.isLt,finite_prefix_value]
      have hpow : 0<2^M := by positivity
      have he : 2^M-1+(∑ k : Fin M, if bits k then 2^k.val else 0)=
          (∑ k : Fin M, if bits k then 2^k.val else 0)+2^M-1 := by omega
      rw [he]

end
end E2.ExactClock
