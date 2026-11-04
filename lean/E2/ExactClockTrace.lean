import E2.ExactClockDigits

namespace E2.ExactClock
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

theorem expansion (a p t : A) (ht : star t*t=1 ∧ t*star t=1)
    (haff : t*a*star t=(4:ℂ) • a-(3:ℂ) • p) (M : ℕ) :
    a=(∑ j ∈ Finset.range M, ((3:ℂ)*(4:ℂ)^(-(j+1:ℤ))) • ctranslate t p j)+
      ((4:ℂ)^(-(M:ℤ))) • ctranslate t a M := by
  have hstep : a=(3/4:ℂ) • p+(1/4:ℂ) • ctranslate t a 1 := by
    simp only [ctranslate,pow_one,haff]
    module
  have h (M : ℕ) :
      a=(∑ j ∈ Finset.range M, ((3:ℂ)*(1/4:ℂ)^(j+1)) • ctranslate t p j)+
        (1/4:ℂ)^M • ctranslate t a M := by
    induction M with
    | zero => simp [ctranslate]
    | succ M ih =>
      have hm := congrArg (fun z : A => ctranslate t z M) hstep
      have hAdd (a b : A) : ctranslate t (a+b) M=ctranslate t a M+ctranslate t b M := by
        simp only [ctranslate,mul_add,add_mul]
      rw [hAdd,shift_smul,shift_smul,shift_shift] at hm
      rw [show 1+M=M+1 by omega] at hm
      calc
        a = (∑ j ∈ Finset.range M, ((3:ℂ)*(1/4:ℂ)^(j+1)) • ctranslate t p j)+
          (1/4:ℂ)^M • ((3/4:ℂ) • ctranslate t p M+(1/4:ℂ) • ctranslate t a (M+1)) := by
            rw [←hm]; exact ih
        _ = _ := by rw [Finset.sum_range_succ]; simp only [smul_add,smul_smul,pow_succ]; module
  have hw (j : ℕ) : (4:ℂ)^(-(j:ℤ))=(1/4:ℂ)^j := by
    simp only [zpow_neg,zpow_natCast,inv_pow,one_div]
  have hw' (j : ℕ) : (4:ℂ)^(-(j+1:ℤ))=(1/4:ℂ)^(j+1) := by
    simpa only [Int.natCast_add,Int.natCast_one] using hw (j+1)
  simpa only [hw,hw'] using h M

 theorem trace_half (τ : TracialState A) (p x q : A) (hxx : x*x=1)
    (hflip : x*p*x=1-p) (hcomm : x*q=q*x) (bit : Bool) :
    τ.toLinearMap ((if bit then p else 1-p)*q)=(1/2:ℂ)*τ.toLinearMap q := by
  have he : τ.toLinearMap ((1-p)*q)=τ.toLinearMap (p*q) := by
    rw [←hflip]
    calc
      _ = τ.toLinearMap (x*((p*q)*x)) := by congr 1; noncomm_ring [hcomm]
      _ = τ.toLinearMap (((p*q)*x)*x) := τ.cyclic _ _
      _ = τ.toLinearMap (p*q) := by rw [mul_assoc,hxx,mul_one]
  have hs : τ.toLinearMap q=τ.toLinearMap (p*q)+τ.toLinearMap ((1-p)*q) := by
    rw [←map_add]; congr 1; noncomm_ring
  rw [he] at hs
  cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true,he] <;> linear_combination -(1/2:ℂ)*hs

 theorem cylinder_succ (p : ℕ → A) (M : ℕ) (bits : Fin (M+1) → Bool) :
    cylinder p (M+1) bits=(if bits 0 then p 0 else 1-p 0)*
      cylinder (fun j => p (j+1)) M (fun j => bits j.succ) := by
  simp only [cylinder,List.finRange_succ,List.map_cons,List.map_map,List.prod_cons,
    Fin.val_zero,Fin.val_succ,Function.comp_def]

 theorem fair_cylinder (τ : TracialState A) (p x : ℕ → A)
    (hxx : ∀ j, x j*x j=1) (hflip : ∀ j, x j*p j*x j=1-p j)
    (hcomm : ∀ j l, j<l → x j*p l=p l*x j) :
    ∀ M bits, τ.toLinearMap (cylinder p M bits)=(2:ℂ)^(-(M:ℤ)) := by
  intro M
  induction M generalizing p x with
  | zero => intro bits; simp [cylinder,τ.normalized]
  | succ M ih =>
    intro bits
    rw [cylinder_succ]
    have hc : x 0*cylinder (fun j => p (j+1)) M (fun j => bits j.succ)=
        cylinder (fun j => p (j+1)) M (fun j => bits j.succ)*x 0 := by
      apply Commute.list_prod_right
      intro q hq
      simp only [cylinder,List.mem_map] at hq
      obtain ⟨j,hj,rfl⟩ := hq
      split_ifs
      · exact hcomm 0 _ (by omega)
      · exact (Commute.one_right _).sub_right (hcomm 0 _ (by omega))
    rw [trace_half τ (p 0) (x 0) _ (hxx 0) (hflip 0) hc (bits 0)]
    rw [ih (fun j => p (j+1)) (fun j => x (j+1)) (fun j => hxx (j+1))
      (fun j => hflip (j+1)) (fun j l h => hcomm (j+1) (l+1) (by omega))]
    simp only [Int.natCast_add,Int.natCast_one,zpow_neg,zpow_add₀ (by norm_num : (2:ℂ)≠0),zpow_one]
    ring

end
end E2.ExactClock

