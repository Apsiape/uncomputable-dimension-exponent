import E2.ExactClockNoTop
import E2.ExactTraceSquareCommutators

namespace E2.ExactClock
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem top_flip_square_orthogonal (p x : ℕ → A) (e : A)
    (he : star e=e)
    (hp : ∀ j, star (p j)=p j)
    (hx : ∀ j, star (x j)=x j ∧ x j*x j=1)
    (hpe : ∀ j, p j*e=e)
    (hflip : ∀ j, x j*p j*x j=1-p j)
    (hcomm : ∀ j k, j<k → x j*p k=p k*x j) :
    ∀ i j, star (x i*e)*(x j*e)=if i=j then e*e else 0 := by
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
    simp only [mul_assoc,←mul_assoc (x i) (x i),(hx i).2,one_mul]
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hzero i j hlt
    · have h := congrArg star (hzero j i hgt)
      simpa only [star_mul,star_star,star_zero] using h

/-- Weak complex faithfulness still excludes every self-adjoint top-supported
element. The square commutator argument avoids any continuity assumption. -/
theorem faithful_top_selfadjoint_zero (m : ExactModel clockPresentation A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (b : A) (hb : IsSelfAdjoint b) (hab : m.value 0*b=b) : b=0 := by
  let r : ℝ := (‖b‖+1)⁻¹
  have hr : 0<r := inv_pos.mpr (by positivity)
  let c : A := r • b
  have hc : IsSelfAdjoint c := (IsSelfAdjoint.all r).smul hb
  have hcn : ‖c‖≤1 := by
    change ‖r • b‖≤1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    change (‖b‖+1)⁻¹*‖b‖≤1
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_one (by positivity : 0<‖b‖+1)).mpr (by linarith)
  let x := ctranslate (m.value 2) (m.value 3)
  let p := ctranslate (m.value 2) (m.value 1)
  have hx : ∀ j, star (x j)=x j ∧ x j*x j=1 := fun j =>
    shift_reflection _ _ (m.domains 2) (m.domains 3) j
  have hp : ∀ j, star (p j)=p j := by
    intro j
    simp only [p,shift_star,(m.domains 1).1]
  have hpc : ∀ j, p j*c=c := by
    intro j
    change p j*(r • b)=r • b
    rw [mul_smul_comm,model_top_digit m b hab j]
  have hd := model_digits m
  have horth := top_flip_square_orthogonal p x c hc.star_eq hp hx hpc hd.2.2.2.1 hd.2.2.2.2.1
  have hz : m.state.toLinearMap (c*c)=0 := by
    apply ExactTrace.orthogonal_square_trace_zero m.state.toLinearMap m.state.cyclic c hc hcn x hx
    intro i j hij
    have h := horth i j
    rw [if_neg hij] at h
    simpa only [star_mul,hc.star_eq,(hx i).1,mul_assoc] using h
  have hcz : c=0 := faithful c (by rwa [hc.star_eq])
  exact (smul_eq_zero.mp hcz).resolve_left hr.ne'

/-- Cancellation of the exact guard, under the frozen weak state and its exact
complex faithfulness premise. -/
theorem guard_cancel (m : ExactModel clockPresentation A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (z : A) (hz : z*(1-m.value 0)=0) : z=0 := by
  have hstar : m.value 0*star z=star z := by
    have h := congrArg star hz
    simp only [star_mul,star_sub,star_one,(m.domains 0).1.star_eq,star_zero,sub_mul,one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hh : star z*z=0 := faithful_top_selfadjoint_zero m faithful (star z*z)
    (IsSelfAdjoint.star_mul_self z) (by rw [←mul_assoc,hstar])
  exact star_mul_self_eq_zero.mp hh

end
end E2.ExactClock
