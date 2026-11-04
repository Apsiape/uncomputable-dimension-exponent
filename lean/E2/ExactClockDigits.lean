import E2.ExactModelDefs
import E2.ExactClockSpectral

namespace E2.ExactClock
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

theorem shift_zero (t a : A) : ctranslate t a 0=a := by simp [ctranslate]
theorem shift_succ (t a : A) (j : ℕ) :
    ctranslate t a (j+1)=t*ctranslate t a j*star t := by
  simp only [ctranslate,pow_succ' t j,pow_succ (star t) j,mul_assoc]

theorem shift_one (t : A) (ht : star t*t=1 ∧ t*star t=1) (j : ℕ) :
    ctranslate t (1:A) j=1 := by
  induction j with
  | zero => simp [ctranslate]
  | succ j ih => rw [shift_succ,ih,mul_one,ht.2]

theorem shift_mul (t a b : A) (ht : star t*t=1 ∧ t*star t=1) (j : ℕ) :
    ctranslate t (a*b) j=ctranslate t a j*ctranslate t b j := by
  induction j with
  | zero => simp [ctranslate]
  | succ j ih =>
    rw [shift_succ,ih,shift_succ,shift_succ]
    simp only [mul_assoc,←mul_assoc (star t) t,ht.1,one_mul]

theorem shift_sub (t a b : A) (j : ℕ) :
    ctranslate t (a-b) j=ctranslate t a j-ctranslate t b j := by
  simp only [ctranslate,mul_sub,sub_mul]

theorem shift_smul (t a : A) (r : ℂ) (j : ℕ) :
    ctranslate t (r • a) j=r • ctranslate t a j := by
  simp only [ctranslate,mul_smul_comm,smul_mul_assoc]

theorem shift_shift (t a : A) (i j : ℕ) :
    ctranslate t (ctranslate t a i) j=ctranslate t a (i+j) := by
  induction j with
  | zero => simp [ctranslate]
  | succ j ih => rw [shift_succ,ih,Nat.add_succ,shift_succ]

theorem shift_star (t a : A) (j : ℕ) :
    star (ctranslate t a j)=ctranslate t (star a) j := by
  simp only [ctranslate,star_mul,star_pow,star_star,mul_assoc]

theorem shift_reflection (t x : A) (ht : star t*t=1 ∧ t*star t=1)
    (hx : star x=x ∧ x*x=1) (j : ℕ) :
    star (ctranslate t x j)=ctranslate t x j ∧ ctranslate t x j*ctranslate t x j=1 := by
  constructor
  · rw [shift_star,hx.1]
  · rw [←shift_mul t x x ht j,hx.2,shift_one t ht j]

theorem digits (a p t : A) (ha : IsSelfAdjoint a)
    (ht : star t*t=1 ∧ t*star t=1) (hp : cfc digitFunction a=p)
    (htail : cfc tailFunction a=t*a*star t) :
    ∀ j, ctranslate t p j=cfc (digitAt j) a := by
  intro j
  induction j with
  | zero =>
    have hf : digitAt 0=digitFunction := by funext x; simp [digitAt]
    rw [shift_zero,hf]; exact hp.symm
  | succ j ih =>
    rw [shift_succ,ih,←conjugate t a ht ha _ (digitAt_lipschitz j).continuous,←htail,
      ←cfc_comp (digitAt j) tailFunction a ha (digitAt_lipschitz j).continuous.continuousOn
        tailFunction_lipschitz.continuous.continuousOn]
    congr 1

theorem own_flip (p t x : A) (ht : star t*t=1 ∧ t*star t=1)
    (hflip : x*p*x=1-p) (j : ℕ) :
    ctranslate t x j*ctranslate t p j*ctranslate t x j=1-ctranslate t p j := by
  rw [←shift_mul t x p ht j,←shift_mul t (x*p) x ht j,hflip,shift_sub,shift_one t ht j]

theorem triangular (a p t x : A) (ha : IsSelfAdjoint a)
    (ht : star t*t=1 ∧ t*star t=1) (hp : cfc digitFunction a=p)
    (htail : cfc tailFunction a=t*a*star t)
    (hcomm : x*(t*a*star t)=(t*a*star t)*x) :
    ∀ j l, j<l → ctranslate t x j*ctranslate t p l=ctranslate t p l*ctranslate t x j := by
  intro j l hjl
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_lt hjl
  subst l
  have he : ctranslate t p (k+1)=cfc (digitAt k) (t*a*star t) := by
    rw [shift_succ,digits a p t ha ht hp htail k,
      conjugate t a ht ha _ (digitAt_lipschitz k).continuous]
  have hc : x*ctranslate t p (k+1)=ctranslate t p (k+1)*x := by
    rw [he]
    exact (Commute.cfc_real (show Commute (t*a*star t) x from hcomm.symm) (digitAt k)).eq.symm
  have hj := congrArg (fun z : A => ctranslate t z j) hc
  rw [shift_mul t _ _ ht j,shift_mul t _ _ ht j,shift_shift] at hj
  convert hj using 1 <;> congr 2 <;> omega

end
end E2.ExactClock


