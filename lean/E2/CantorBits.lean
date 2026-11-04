import E2.CantorScalar

namespace E2
noncomputable section
open scoped BigOperators

def binaryPrefix (b : ℕ → Bool) (M : ℕ) : ℕ :=
  ∑ k ∈ Finset.range M, if b k then 2^k else 0

theorem binaryPrefix_zero (b : ℕ → Bool) : binaryPrefix b 0=0 := by simp [binaryPrefix]
theorem binaryPrefix_succ (b : ℕ → Bool) (M : ℕ) :
    binaryPrefix b (M+1)=binaryPrefix b M+(if b M then 2^M else 0) := by
  exact Finset.sum_range_succ _ _

theorem binaryPrefix_lt (b : ℕ → Bool) (M : ℕ) : binaryPrefix b M<2^M := by
  induction M with
  | zero => simp [binaryPrefix]
  | succ M ih =>
    rw [binaryPrefix_succ,pow_succ]
    have hp : 0<2^M := by positivity
    split <;> omega

theorem binaryPrefix_congr (b c : ℕ → Bool) (M : ℕ)
    (h : ∀ k<M, b k=c k) : binaryPrefix b M=binaryPrefix c M := by
  apply Finset.sum_congr rfl
  intro k hk
  rw [h k (Finset.mem_range.mp hk)]

theorem addBits_eq (i : ℕ) (b : ℕ → Bool) (j : ℕ) :
    addBits i b j=decide (((i+binaryPrefix b (j+1))/2^j)%2=1) := rfl

theorem addBits_value (i : ℕ) (b : ℕ → Bool) (j : ℕ) :
    (if addBits i b j then 2^j else 0)=2^j*((i+binaryPrefix b (j+1))/2^j%2) := by
  rw [addBits_eq]
  have hm := Nat.mod_lt ((i+binaryPrefix b (j+1))/2^j) (by decide : 0<2)
  by_cases h : (i+binaryPrefix b (j+1))/2^j%2=1 <;> simp [h]
  have hz : (i+binaryPrefix b (j+1))/2^j%2=0 := by omega
  simp [hz]

/-- Output prefixes are reduction of the translated input modulo 2^M. -/
theorem binaryPrefix_addBits (i : ℕ) (b : ℕ → Bool) (M : ℕ) :
    binaryPrefix (addBits i b) M=(i+binaryPrefix b M)%2^M := by
  induction M with
  | zero => simp [binaryPrefix,Nat.mod_one]
  | succ M ih =>
    rw [binaryPrefix_succ,ih,addBits_value]
    have hmod : (i+binaryPrefix b M)%2^M=(i+binaryPrefix b (M+1))%2^M := by
      rw [binaryPrefix_succ]
      split <;> simp [Nat.add_mod]
    rw [hmod]
    simpa only [pow_succ] using
      (Nat.mod_mul (a:=2^M) (b:=2) (x:=i+binaryPrefix b (M+1))).symm

/-- Addition never changes agreement on a fixed binary prefix. -/
theorem addBits_prefix_agree (i : ℕ) (b c : ℕ → Bool) (M : ℕ)
    (h : ∀ k<M, b k=c k) : ∀ k<M, addBits i b k=addBits i c k := by
  intro k hk
  have he := binaryPrefix_congr b c (k+1) (fun l hl => h l (by omega))
  simp only [addBits_eq,he]

theorem addBits_comp (i k : ℕ) (b : ℕ → Bool) :
    addBits i (addBits k b)=addBits (i+k) b := by
  funext j
  rw [addBits_eq,addBits_eq,binaryPrefix_addBits]
  have hmod : (i+(k+binaryPrefix b (j+1))%2^(j+1))%2^(j+1) =
      ((i+k)+binaryPrefix b (j+1))%2^(j+1) := by
    simp [Nat.add_mod,Nat.add_assoc]
  have he : (i+(k+binaryPrefix b (j+1))%2^(j+1))/2^j%2 =
      ((i+k)+binaryPrefix b (j+1))/2^j%2 := by
    rw [← Nat.mod_mul_right_div_self,← Nat.mod_mul_right_div_self]
    simpa only [← pow_succ] using congrArg (fun n => n/2^j) hmod
  rw [he]

theorem addBits_zero (b : ℕ → Bool) : addBits 0 b=b := by
  funext j
  rw [addBits_eq,binaryPrefix_succ]
  have hlt := binaryPrefix_lt b j
  have hp : 0<2^j := by positivity
  cases hb : b j
  · simp [hb,Nat.div_eq_of_lt hlt]
  · simp only [hb,Bool.true_eq,reduceIte,Nat.zero_add]
    rw [Nat.add_div_right _ hp,Nat.div_eq_of_lt hlt]
    decide

theorem binaryPrefix_head (b : ℕ → Bool) (M : ℕ) :
    binaryPrefix b (M+1)=(if b 0 then 1 else 0)+2*binaryPrefix (dropBits b 1) M := by
  induction M with
  | zero => simp [binaryPrefix]
  | succ M ih =>
    rw [binaryPrefix_succ b (M+1),ih,binaryPrefix_succ (dropBits b 1) M]
    change (if b 0 then 1 else 0)+2*binaryPrefix (dropBits b 1) M+
      (if b (M+1) then 2^(M+1) else 0) =
      (if b 0 then 1 else 0)+2*(binaryPrefix (dropBits b 1) M+
        (if b (M+1) then 2^M else 0))
    rw [pow_succ]
    cases hb : b (M+1) <;> simp only [hb,Bool.false_eq_true,Bool.true_eq,reduceIte] <;> ring

theorem addBits_one_head (b : ℕ → Bool) : addBits 1 b 0= !(b 0) := by
  rw [addBits_eq,binaryPrefix_head]
  cases hb : b 0 <;> simp [hb,binaryPrefix]

/-- Recursive binary carry, with no truncation or overflow assumption. -/
theorem addBits_one_tail (b : ℕ → Bool) :
    dropBits (addBits 1 b) 1=addBits (if b 0 then 1 else 0) (dropBits b 1) := by
  funext j
  change addBits 1 b (j+1)=addBits (if b 0 then 1 else 0) (dropBits b 1) j
  rw [addBits_eq,addBits_eq,binaryPrefix_head]
  cases hb : b 0 <;> simp only [hb,Bool.false_eq_true,Bool.true_eq,reduceIte]
  · rw [pow_succ',← Nat.div_div_eq_div_mul]
    have he : (1+(0+2*binaryPrefix (dropBits b 1) (j+1)))/2 =
        binaryPrefix (dropBits b 1) (j+1) := by omega
    rw [he,Nat.zero_add]
  · rw [pow_succ',← Nat.div_div_eq_div_mul]
    have he : (1+(1+2*binaryPrefix (dropBits b 1) (j+1)))/2 =
        1+binaryPrefix (dropBits b 1) (j+1) := by omega
    rw [he]

end
end E2
