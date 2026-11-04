import E2.ExactClockModel
import E2.ExactTraceCommutators

namespace E2.ExactClock
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem digitAt_one (j : ℕ) : digitAt j 1=1 := by
  have h : ∀ n : ℕ, tailFunction^[n] (1:ℝ)=1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih]
      norm_num [tailFunction,digitFunction]
  unfold digitAt
  rw [h]
  norm_num [digitFunction]

/-- A top eigenspace lies under each exact clock digit, as an algebra identity. -/
theorem model_top_digit (m : ExactModel clockPresentation A)
    (e : A) (hae : m.value 0*e=e) (j : ℕ) :
    ctranslate (m.value 2) (m.value 1) j*e=e := by
  rw [(model_digits m).2.1 j]
  have h := intertwines (m.value 0) 1 e (m.domains 0).1 (IsSelfAdjoint.one A)
    (by simpa only [mul_one] using hae) (digitAt j) (digitAt_lipschitz j).continuous
  simpa only [cfc_apply_one,digitAt_one,map_one,mul_one] using h

/-- Triangular flips produce orthogonal equivalent copies of a top projection. -/
theorem top_flip_orthogonal (p x : ℕ → A) (e : A)
    (he : star e=e) (hee : e*e=e)
    (hp : ∀ j, star (p j)=p j)
    (hx : ∀ j, star (x j)=x j ∧ x j*x j=1)
    (hpe : ∀ j, p j*e=e)
    (hflip : ∀ j, x j*p j*x j=1-p j)
    (hcomm : ∀ j k, j<k → x j*p k=p k*x j) :
    ∀ i j, star (x i*e)*(x j*e)=if i=j then e else 0 := by
  have hzero (i j : ℕ) (hij : i<j) : star (x i*e)*(x j*e)=0 := by
    have hep : e*p j=e := by
      have h := congrArg star (hpe j)
      simpa only [star_mul,he,hp j] using h
    have hxe : p j*x j*e=0 := by
      have h := congrArg (fun z => x j*z) (hflip j)
      have hf : p j*x j=x j*(1-p j) := by
        simpa only [←mul_assoc,(hx j).2,one_mul] using h
      rw [hf,mul_assoc,sub_mul,one_mul,hpe,sub_self,mul_zero]
    simp only [star_mul,he,(hx i).1]
    calc
      e*x i*(x j*e) = (e*p j)*x i*(x j*e) := by rw [hep]
      _ = e*((p j*x i)*(x j*e)) := by simp only [mul_assoc]
      _ = e*((x i*p j)*(x j*e)) := by rw [hcomm i j hij]
      _ = e*(x i*(p j*x j*e)) := by simp only [mul_assoc]
      _ = 0 := by rw [hxe,mul_zero,mul_zero]
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [ite_true,star_mul,he,(hx i).1]
    simp only [mul_assoc,←mul_assoc (x i) (x i),(hx i).2,one_mul,hee]
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hzero i j hlt
    · have h := congrArg star (hzero j i hgt)
      simpa only [star_mul,star_star,star_zero] using h

/-- The full complex no-top clause holds under the unchanged weak state.
Cyclicity suffices: the projection is a finite sum of commutators. -/
theorem model_top_projection (m : ExactModel clockPresentation A)
    (e : A) (he : star e=e) (hee : e*e=e) (hae : m.value 0*e=e) :
    m.state.toLinearMap e=0 := by
  let x := ctranslate (m.value 2) (m.value 3)
  let p := ctranslate (m.value 2) (m.value 1)
  have hx : ∀ j, star (x j)=x j ∧ x j*x j=1 := fun j =>
    shift_reflection _ _ (m.domains 2) (m.domains 3) j
  have hd := model_digits m
  apply ExactTrace.orthogonal_copies_trace_zero m.state.toLinearMap m.state.cyclic e (fun j => x j*e)
  · intro j
    simp only [mul_assoc,hee]
  · apply top_flip_orthogonal p x e he hee _ hx (model_top_digit m e hae) hd.2.2.2.1 hd.2.2.2.2.1
    intro j
    simp only [p,shift_star,(m.domains 1).1]

end
end E2.ExactClock
