import E2.CompilerCertificates

/-! Finite ring certificates for the two conjugacy gadget converses in Section 3.
These are polynomial identities before imposing any relation. -/
namespace E2.CompilerGadgets
variable {A : Type*} [Ring A]

theorem six_context_certificate (a b c d₁ d₂ d₃ d₄ d₅ d₆ d₇ : A) :
    a*b*a-c =
      (a-d₁*d₂)*b*a +
      d₁*d₂*(b-d₂*d₃)*a +
      d₁*(d₂*d₂-1)*d₃*a +
      d₁*d₃*(a-d₅*d₆) +
      d₁*(d₃*d₅-d₄)*d₆ +
      (d₁*d₄-d₇)*d₆ + (d₇*d₆-c) := by
  noncomm_ring

theorem six_context_converse (a b c d₁ d₂ d₃ d₄ d₅ d₆ d₇ : A)
    (ha : a = d₁*d₂) (hb : b = d₂*d₃) (h₂ : d₂*d₂=1)
    (ha' : a = d₅*d₆) (h₄ : d₃*d₅=d₄)
    (h₇ : d₁*d₄=d₇) (hc : d₇*d₆=c) : a*b*a=c := by
  apply sub_eq_zero.mp
  rw [six_context_certificate a b c d₁ d₂ d₃ d₄ d₅ d₆ d₇]
  simp only [sub_eq_zero.mpr ha, sub_eq_zero.mpr hb, h₂, sub_eq_zero.mpr ha',
    sub_eq_zero.mpr h₄, sub_eq_zero.mpr h₇, sub_eq_zero.mpr hc,
    sub_self, mul_zero, zero_mul, add_zero]

/-- The first converse step, exposing all residuals of the conjugacy and the
commutation between the auxiliary swap and the original conjugator. -/
theorem general_z_certificate (a f w y z t : A) :
    a*z*a-t = a*(z-f*y*f)*a + (a*f-w)*y*f*a +
      w*y*(f*a-w) + (w*y*w-t) := by
  noncomm_ring

/-- Conjugating a residual by an involution, with its square residual exposed. -/
theorem swap_certificate (f y z : A) :
    y-f*z*f = f*(f*y*f-z)*f -
      (f*f-1)*y*(f*f) - y*(f*f-1) := by
  noncomm_ring

theorem general_y_certificate (a f y z y' z' : A) :
    a*y*a-y' = a*(y-f*z*f)*a +
      (a*f-f*a)*z*f*a + f*a*z*(f*a-a*f) +
      f*(a*z*a-z')*f + (f*z'*f-y') := by
  noncomm_ring

theorem general_product_certificate (a x₂ x₃ y₂ z₂ y₃ z₃ : A) :
    a*x₂*a-x₃ = a*(x₂-y₂*z₂)*a +
      (a*y₂*a-y₃)*(a*z₂*a) + y₃*(a*z₂*a-z₃) +
      (y₃*z₃-x₃) - a*y₂*(a*a-1)*z₂*a := by
  noncomm_ring

/-- Full converse of the general gadget, after the parity contexts have
identified the displayed products. This works in every ring. -/
theorem general_converse (a f w x₂ x₃ y₂ z₂ y₃ z₃ : A)
    (ha : a*a=1) (hf : f*f=1) (haf : a*f=f*a) (hw : w=a*f)
    (h₂ : f*y₂*f=z₂) (h₃ : f*y₃*f=z₃) (hconj : w*y₂*w=z₃)
    (hx₂ : x₂=y₂*z₂) (hx₃ : x₃=y₃*z₃) : a*x₂*a=x₃ := by
  have hfa : f*a=w := by rw [hw, haf]
  have hz : a*z₂*a-z₃=0 := by
    rw [general_z_certificate a f w y₂ z₂ z₃]
    simp only [h₂, ← hw, hfa, hconj, sub_self, mul_zero, zero_mul, add_zero]
  have hy₂ : y₂-f*z₂*f=0 := by
    rw [swap_certificate, h₂, hf]
    simp
  have hy₃ : f*z₃*f-y₃=0 := by
    have h := swap_certificate f y₃ z₃
    rw [h₃, hf] at h
    simp only [sub_self, mul_zero, zero_mul, sub_zero] at h
    exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
  have hy : a*y₂*a-y₃=0 := by
    rw [general_y_certificate a f y₂ z₂ y₃ z₃]
    simp only [hy₂, haf, hz, hy₃, sub_self, mul_zero, zero_mul, add_zero]
  apply sub_eq_zero.mp
  rw [general_product_certificate a x₂ x₃ y₂ z₂ y₃ z₃]
  simp only [hx₂, hx₃, ha, hy, hz, sub_self, mul_zero, zero_mul, add_zero, sub_zero]

end E2.CompilerGadgets
