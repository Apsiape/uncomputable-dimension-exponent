import E2.ExactIncrementAlgebra
import E2.ExactIncrementBits
import E2.ExactClockTrace

namespace E2.ExactClock
noncomputable section
variable {A : Type*} [CStarAlgebra A]

def clockPrefix (p : ℕ → A) (j M : ℕ) (b : ℕ → Bool) : A :=
  cylinder (fun k => p (j+k)) M (fun i => b i.val)

theorem prefix_zero (p : ℕ → A) (j : ℕ) (b : ℕ → Bool) : clockPrefix p j 0 b=1 := by
  simp [clockPrefix,cylinder]

theorem prefix_succ (p : ℕ → A) (j M : ℕ) (b : ℕ → Bool) :
    clockPrefix p j (M+1) b=(if b 0 then p j else 1-p j)*clockPrefix p (j+1) M (dropBits b 1) := by
  rw [clockPrefix,cylinder_succ]
  simp only [Nat.add_zero,Fin.val_zero]
  congr 1
  unfold clockPrefix
  congr 1
  · funext k; congr 1; omega

theorem prefix_commute (p : ℕ → A) (j M : ℕ) (b : ℕ → Bool) (z : A)
    (hz : ∀ k, z*p (j+k)=p (j+k)*z) : z*clockPrefix p j M b=clockPrefix p j M b*z := by
  apply Commute.list_prod_right
  intro q hq
  simp only [clockPrefix,cylinder,List.mem_map] at hq
  obtain ⟨i,hi,rfl⟩ := hq
  split_ifs
  · exact hz i.val
  · exact (Commute.one_right _).sub_right (hz i.val)

theorem prefix_congr (p : ℕ → A) (j M : ℕ) (b c : ℕ → Bool)
    (h : ∀ k<M, b k=c k) : clockPrefix p j M b=clockPrefix p j M c := by
  unfold clockPrefix cylinder
  congr 2
  funext i
  dsimp only
  simp only [h i.val i.isLt]

/-- The recursion increments every finite clockPrefix, independently of the state. -/
theorem prefix_forward (p x v : ℕ → A)
    (hp : ∀ j, star (p j)=p j ∧ p j*p j=p j)
    (hx : ∀ j, star (x j)=x j ∧ x j*x j=1)
    (hv : ∀ j, star (v j)*v j=1 ∧ v j*star (v j)=1)
    (hpp : ∀ i j, p i*p j=p j*p i)
    (hxp : ∀ i j, i<j → x i*p j=p j*x i)
    (hflip : ∀ j, x j*p j*x j=1-p j)
    (hcarry : ∀ j, v (j+1)*p j=p j*v (j+1))
    (hrec : ∀ j, v j=x j*((1-p j)+v (j+1)*p j)) :
    ∀ M j b, v j*clockPrefix p j M b*star (v j)=clockPrefix p j M (addBits 1 b) := by
  intro M
  induction M with
  | zero => intro j b; rw [prefix_zero,prefix_zero,mul_one,(hv j).2]
  | succ M ih =>
    intro j b
    let q := clockPrefix p (j+1) M (dropBits b 1)
    let q' := clockPrefix p (j+1) M (addBits 1 (dropBits b 1))
    have hq : q*p j=p j*q := (prefix_commute p (j+1) M _ (p j) (fun k => hpp _ _)).symm
    have hq' : q'*p j=p j*q' := (prefix_commute p (j+1) M _ (p j) (fun k => hpp _ _)).symm
    have hxq : x j*q=q*x j := prefix_commute p (j+1) M _ _ (fun k => hxp _ _ (by omega))
    have hxq' : x j*q'=q'*x j := prefix_commute p (j+1) M _ _ (fun k => hxp _ _ (by omega))
    have h := controlled_forward (p j) (x j) (v (j+1)) ((1-p j)+v (j+1)*p j) q q'
      (hp j) (hx j) (hv (j+1)) rfl (hcarry j) hq hq' hxq hxq' (hflip j)
      (ih (j+1) (dropBits b 1)) (b 0)
    rw [←hrec j] at h
    rw [prefix_succ,prefix_succ,addBits_one_head,addBits_one_tail]
    cases hb : b 0 <;> simpa only [hb,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,
      addBits_zero,q,q'] using h

/-- Inverse form, using the exact finite-clockPrefix decrement required by the
frozen statement. -/
theorem prefix_backward (p x v : ℕ → A)
    (hp : ∀ j, star (p j)=p j ∧ p j*p j=p j)
    (hx : ∀ j, star (x j)=x j ∧ x j*x j=1)
    (hv : ∀ j, star (v j)*v j=1 ∧ v j*star (v j)=1)
    (hpp : ∀ i j, p i*p j=p j*p i)
    (hxp : ∀ i j, i<j → x i*p j=p j*x i)
    (hflip : ∀ j, x j*p j*x j=1-p j)
    (hcarry : ∀ j, v (j+1)*p j=p j*v (j+1))
    (hrec : ∀ j, v j=x j*((1-p j)+v (j+1)*p j))
    (M j : ℕ) (b : ℕ → Bool) :
    star (v j)*clockPrefix p j M b*v j=clockPrefix p j M (addBits (2^M-1) b) := by
  have hpow : 0<2^M := by positivity
  have hf := prefix_forward p x v hp hx hv hpp hxp hflip hcarry hrec M j (addBits (2^M-1) b)
  have he : clockPrefix p j M (addBits 1 (addBits (2^M-1) b))=clockPrefix p j M b := by
    rw [addBits_comp,show 1+(2^M-1)=2^M by omega]
    apply prefix_congr
    intro k hk
    rw [addBits_full_prefix _ M b k hk, Nat.add_comm,bit_period _ M k hk]
    have hz := addBits_full_prefix 0 M b k hk
    simpa only [addBits_zero,Nat.zero_add] using hz.symm
  rw [he] at hf
  calc
    _ = star (v j)*(v j*clockPrefix p j M (addBits (2^M-1) b)*star (v j))*v j := by rw [hf]
    _ = _ := by simp only [mul_assoc,←mul_assoc (star (v j)) (v j),(hv j).1,one_mul,mul_one]

end
end E2.ExactClock
