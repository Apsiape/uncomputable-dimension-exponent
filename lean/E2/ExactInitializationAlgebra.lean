import E2.ExactModelDefs

namespace E2.ExactForcing
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem address_decode (σ : A →⋆ₐ[ℂ] A) (a b H L : A) (r : ℂ) (E : ℕ → A)
    (haa : a*a=a) (hbb : b*b=b) (hab : a*b=0) (hba : b*a=0)
    (hE0 : E 0=b) (hEs : ∀ n, E (n+1)=a*σ (E n))
    (hEa : ∀ n, E n*a=a*E n)
    (hH : H=b+a*σ H) (hL : L=(1-a)+r • (a*σ L)) :
    ∀ n, E n*H=E n ∧ E n*L=r^n • E n := by
  intro n
  induction n with
  | zero =>
    constructor
    · rw [hE0,hH,mul_add,←mul_assoc,hbb,hba,zero_mul,add_zero]
    · rw [hE0,hL,mul_add,mul_sub,mul_one,hba,sub_zero,mul_smul_comm,←mul_assoc,hba,
        zero_mul,smul_zero,add_zero,pow_zero,one_smul]
  | succ n ih =>
    have h0 : E (n+1)*a=E (n+1) := by rw [hEa,hEs,←mul_assoc,haa]
    have h1 : E (n+1)*b=0 := by rw [←h0,mul_assoc,hab,mul_zero]
    have h2 : E (n+1)*(1-a)=0 := by rw [mul_sub,mul_one,h0,sub_self]
    constructor
    · rw [hH,mul_add,h1,←mul_assoc,h0,zero_add,hEs,mul_assoc,←map_mul,ih.1]
    · rw [hL,mul_add,h2,mul_smul_comm,←mul_assoc,h0,zero_add,hEs,mul_assoc,←map_mul,ih.2,
        map_smul,mul_smul_comm,smul_smul,pow_succ]
      congr 1
      ring

theorem reset_decode (σ : A →⋆ₐ[ℂ] A) (p q Z : A) (F T : ℕ → A)
    (hpp : p*p=p) (hF0 : F 0=1-p) (hT0 : T 0=1)
    (hFs : ∀ k, F (k+1)=p*σ (F k)) (hTs : ∀ k, T (k+1)=q*σ (T k))
    (hFp : ∀ k, F (k+1)*p=F (k+1)) (hFq : ∀ k, F (k+1)*q=q*F (k+1))
    (hZ : Z=(1-p)+p*q*σ Z) : ∀ k, F k*Z=F k*T k := by
  intro k
  induction k with
  | zero =>
    rw [hF0,hT0,mul_one]
    have hnp : (1-p)*p=0 := by rw [sub_mul,one_mul,hpp,sub_self]
    nth_rw 1 [hZ]
    calc
      _ = (1-p)*(1-p)+((1-p)*p)*q*σ Z := by noncomm_ring
      _ = 1-p := by rw [hnp,zero_mul,zero_mul,add_zero]; noncomm_ring [hpp]
  | succ k ih =>
    have hz : F (k+1)*(1-p)=0 := by rw [mul_sub,mul_one,hFp,sub_self]
    calc
      F (k+1)*Z = F (k+1)*q*σ Z := by nth_rw 1 [hZ]; rw [mul_add,hz,←mul_assoc,←mul_assoc,hFp,zero_add]
      _ = q*p*σ (F k)*σ Z := by rw [hFq,hFs]; simp only [mul_assoc]
      _ = q*p*σ (F k*Z) := by rw [map_mul,mul_assoc]
      _ = q*p*σ (F k*T k) := by rw [ih]
      _ = q*F (k+1)*σ (T k) := by rw [map_mul,hFs]; simp only [mul_assoc]
      _ = F (k+1)*T (k+1) := by rw [←hFq,hTs,mul_assoc]

end
end E2.ExactForcing
