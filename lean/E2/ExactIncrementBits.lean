import E2.CantorBits

namespace E2.ExactClock
noncomputable section
open scoped BigOperators

theorem binaryPrefix_mod (b : ℕ → Bool) (M n : ℕ) (hn : n≤M) :
    binaryPrefix b M%2^n=binaryPrefix b n := by
  induction M with
  | zero =>
    have he : n=0 := by omega
    subst n
    simp [binaryPrefix]
  | succ M ih =>
    by_cases h : n≤M
    · rw [binaryPrefix_succ,Nat.add_mod,ih h]
      have hd : 2^n ∣ 2^M := Nat.pow_dvd_pow 2 h
      split_ifs <;> simp [Nat.mod_eq_zero_of_dvd hd,Nat.mod_eq_of_lt (binaryPrefix_lt b n)]
    · have he : n=M+1 := by omega
      subst n
      exact Nat.mod_eq_of_lt (binaryPrefix_lt b (M+1))

theorem addBits_full_prefix (i M : ℕ) (b : ℕ → Bool) (j : ℕ) (hj : j<M) :
    addBits i b j=decide (((i+binaryPrefix b M)/2^j)%2=1) := by
  rw [addBits_eq]
  have hm : (i+binaryPrefix b (j+1))%2^(j+1)=(i+binaryPrefix b M)%2^(j+1) := by
    rw [Nat.add_mod i (binaryPrefix b (j+1)),Nat.mod_eq_of_lt (binaryPrefix_lt b (j+1))]
    conv_rhs => rw [Nat.add_mod i (binaryPrefix b M),binaryPrefix_mod b M (j+1) (by omega)]
  have he := congrArg (fun n => n/2^j) hm
  simp only [pow_succ,Nat.mod_mul_right_div_self] at he
  rw [he]

theorem bit_period (n M j : ℕ) (hj : j<M) :
    ((n+2^M)/2^j)%2=(n/2^j)%2 := by
  rw [←Nat.mod_mul_right_div_self,←Nat.mod_mul_right_div_self]
  have hd : 2^j*2 ∣ 2^M := by
    rw [←pow_succ]
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,Nat.add_zero,Nat.mod_mod]

def extendBits {M : ℕ} (bits : Fin M → Bool) (j : ℕ) : Bool :=
  if h : j<M then bits ⟨j,h⟩ else false

theorem extendBits_apply {M : ℕ} (bits : Fin M → Bool) (j : Fin M) :
    extendBits bits j.val=bits j := by simp [extendBits]

theorem finite_prefix_value {M : ℕ} (bits : Fin M → Bool) :
    binaryPrefix (extendBits bits) M=∑ k : Fin M, if bits k then 2^k.val else 0 := by
  calc
    binaryPrefix (extendBits bits) M = ∑ k : Fin M, if extendBits bits k.val then 2^k.val else 0 :=
      (Fin.sum_univ_eq_sum_range (fun k => if extendBits bits k then 2^k else 0) M).symm
    _ = _ := by simp only [extendBits_apply]

end
end E2.ExactClock
