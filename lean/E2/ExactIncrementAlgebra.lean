import E2.ExactModelDefs

namespace E2.ExactClock
noncomputable section
variable {A : Type*} [CStarAlgebra A]

/-- A unitary controlled extension that fixes the complementary block has a
unitary carry block, so the carry unitary reduces the control projection. -/
theorem controlled_commutes (p c d : A) (hp : star p=p ∧ p*p=p)
    (hc : star c*c=1 ∧ c*star c=1) (hd : star d*d=1 ∧ d*star d=1)
    (he : d=(1-p)+c*p) : c*p=p*c := by
  have hfix : d*(1-p)=1-p := by
    rw [he]
    noncomm_ring [hp.2]
  have hsfix : star d*(1-p)=1-p := by
    have h := congrArg (fun z => star d*z) hfix
    simpa only [←mul_assoc,hd.1,one_mul] using h.symm
  have hleft : (1-p)*d=1-p := by
    have h := congrArg star hsfix
    simpa only [star_mul,star_sub,star_one,hp.1,star_star] using h
  have hdp : d*p=p*d := by
    rw [mul_sub,mul_one] at hfix
    rw [sub_mul,one_mul] at hleft
    exact sub_right_inj.mp (hfix.trans hleft.symm)
  have hedp : d*p=c*p := by
    rw [he]
    noncomm_ring [hp.2]
  have hsdp : p*star d=p*star c := by
    have h := congrArg star hedp
    simpa only [star_mul,hp.1] using h
  have hconj : c*p*star c=p := by
    calc
      _ = d*p*star c := by rw [hedp]
      _ = d*(p*star c) := mul_assoc _ _ _
      _ = d*(p*star d) := by rw [hsdp]
      _ = p*d*star d := by rw [←mul_assoc,hdp]
      _ = p := by rw [mul_assoc,hd.2,mul_one]
  have h := congrArg (fun z => z*c) hconj
  simpa only [mul_assoc,hc.1,mul_one] using h

/-- The two branches of forward binary increment on a commuting tail. -/
theorem controlled_forward (p x c d q q' : A)
    (hp : star p=p ∧ p*p=p) (hx : star x=x ∧ x*x=1)
    (hc : star c*c=1 ∧ c*star c=1) (he : d=(1-p)+c*p)
    (hcp : c*p=p*c) (hqp : q*p=p*q) (hqp' : q'*p=p*q')
    (hxq : x*q=q*x) (hxq' : x*q'=q'*x) (hflip : x*p*x=1-p)
    (hcarry : c*q*star c=q') (bit : Bool) :
    (x*d)*((if bit then p else 1-p)*q)*star (x*d)=
      (if bit then 1-p else p)*(if bit then q' else q) := by
  have hdp : d*p=c*p := by rw [he]; noncomm_ring [hp.2]
  have hdn : d*(1-p)=1-p := by rw [he]; noncomm_ring [hp.2]
  have hps : p*star d=p*star c := by
    have h := congrArg star hdp
    simpa only [star_mul,hp.1] using h
  have hns : (1-p)*star d=1-p := by
    have h := congrArg star hdn
    simpa only [star_mul,star_sub,star_one,hp.1] using h
  have hcp' : p*star c=star c*p := by
    have h := congrArg star hcp
    simpa only [star_mul,hp.1] using h
  have hqn : (1-p)*q=q*(1-p) := by rw [sub_mul,mul_sub,one_mul,mul_one,hqp]
  have hxnx : x*(1-p)*x=p := by
    simp only [mul_sub,sub_mul,mul_one,one_mul,hx.2,hflip]
    abel
  cases bit
  · simp only [Bool.false_eq_true,ite_false,star_mul,hx.1]
    calc
      _ = x*(d*((1-p)*q)*star d)*x := by simp only [mul_assoc]
      _ = x*((1-p)*q)*x := by
        congr 2
        calc
          _ = (1-p)*q*star d := by rw [←mul_assoc d,hdn]
          _ = q*((1-p)*star d) := by rw [hqn,mul_assoc]
          _ = (1-p)*q := by rw [hns,hqn]
      _ = p*q := by
        calc
          _ = (x*(1-p)*x)*q := by simp only [mul_assoc]; rw [←hxq]
          _ = _ := by rw [hxnx]
  · simp only [ite_true,star_mul,hx.1]
    calc
      _ = x*(d*(p*q)*star d)*x := by simp only [mul_assoc]
      _ = x*(p*q')*x := by
        congr 2
        calc
          _ = c*p*q*star d := by rw [←mul_assoc d,hdp]
          _ = c*q*(p*star d) := by simp only [mul_assoc]; rw [←mul_assoc p q,←hqp]; simp only [mul_assoc]
          _ = c*q*(p*star c) := by rw [hps]
          _ = c*(q*p)*star c := by simp only [mul_assoc]
          _ = c*(p*q)*star c := by rw [hqp]
          _ = p*(c*q*star c) := by simp only [←mul_assoc,hcp]
          _ = p*q' := by rw [hcarry]
      _ = (1-p)*q' := by
        calc
          _ = (x*p*x)*q' := by simp only [mul_assoc]; rw [←hxq']
          _ = _ := by rw [hflip]

end
end E2.ExactClock
