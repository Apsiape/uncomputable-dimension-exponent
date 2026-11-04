import E2.ExactClockTrace

namespace E2
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

/-- Lemma 4.1: exact spectral digits, expansion, triangular flips, and fair
cylinders in arbitrary C*-algebras with a tracial state, not just matrices. -/
theorem exact_clock_digits (τ : TracialState A) (a p t x : A)
    (ha : Domain.positiveContraction.HoldsC a) (hp : Domain.projection.HoldsC p)
    (ht : Domain.unitary.HoldsC t) (hx : Domain.reflection.HoldsC x)
    (hap : a*p=p*a) (haff : t*a*star t = (4:ℂ) • a - (3:ℂ) • p)
    (hflip : x*p*x=1-p) (htail : x*(t*a*star t)=(t*a*star t)*x) :
    spectrum ℝ a ⊆ cantorSet ∧
    (∀ j, ctranslate t p j = cfc (digitAt j) a) ∧
    (∀ M, a = (∑ j ∈ Finset.range M, ((3:ℂ)*(4:ℂ)^(-(j+1:ℤ))) • ctranslate t p j) +
      ((4:ℂ)^(-(M:ℤ))) • ctranslate t a M) ∧
    (∀ j, ctranslate t x j * ctranslate t p j * ctranslate t x j = 1-ctranslate t p j) ∧
    (∀ j l, j<l → ctranslate t x j * ctranslate t p l = ctranslate t p l * ctranslate t x j) ∧
    (∀ M bits, τ.toLinearMap (cylinder (ctranslate t p) M bits) = ((2:ℂ)^(-(M:ℤ)))) := by
  have ht' : star t*t=1 ∧ t*star t=1 := ht
  have hx' : star x=x ∧ x*x=1 := hx
  obtain ⟨hσ,hp',htail'⟩ := ExactClock.affine a p t ha.1 ha.2 hp.2 ht' hap haff
  refine ⟨hσ,ExactClock.digits a p t ha.1 ht' hp' htail',
    ExactClock.expansion a p t ht' haff,ExactClock.own_flip p t x ht' hflip,
    ExactClock.triangular a p t x ha.1 ht' hp' htail' htail,?_⟩
  exact ExactClock.fair_cylinder τ (ctranslate t p) (ctranslate t x)
    (fun j => (ExactClock.shift_reflection t x ht' hx' j).2)
    (ExactClock.own_flip p t x ht' hflip)
    (ExactClock.triangular a p t x ha.1 ht' hp' htail' htail)

end
end E2
