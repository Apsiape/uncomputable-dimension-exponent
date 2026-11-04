import E2.ExactClockTheorem
import E2.ExactClockMoments
import E2.ExactTraceHermitian
import E2.ExactPolyEval

namespace E2.ExactClock
noncomputable section
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]

 theorem model_digits (m : ExactModel clockPresentation A) :
    spectrum ℝ (m.value 0) ⊆ cantorSet ∧
    (∀ j, ctranslate (m.value 2) (m.value 1) j = cfc (digitAt j) (m.value 0)) ∧
    (∀ M, m.value 0 = (∑ j ∈ Finset.range M, ((3:ℂ)*(4:ℂ)^(-(j+1:ℤ))) • ctranslate (m.value 2) (m.value 1) j) +
      ((4:ℂ)^(-(M:ℤ))) • ctranslate (m.value 2) (m.value 0) M) ∧
    (∀ j, ctranslate (m.value 2) (m.value 3) j * ctranslate (m.value 2) (m.value 1) j * ctranslate (m.value 2) (m.value 3) j = 1-ctranslate (m.value 2) (m.value 1) j) ∧
    (∀ j l, j<l → ctranslate (m.value 2) (m.value 3) j * ctranslate (m.value 2) (m.value 1) l = ctranslate (m.value 2) (m.value 1) l * ctranslate (m.value 2) (m.value 3) j) ∧
    (∀ M bits, m.state.toLinearMap (cylinder (ctranslate (m.value 2) (m.value 1)) M bits) = ((2:ℂ)^(-(M:ℤ)))) := by
  apply exact_clock_digits m.state
  · exact m.domains 0
  · exact m.domains 1
  · exact m.domains 2
  · exact m.domains 3
  · have h := m.equations (pc (.var 0) (.var 1)) (by simp [clockPresentation,clockRelations])
    exact sub_eq_zero.mp (by simpa only [pc,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_var] using h)
  · have h := m.equations (conjP (.var 2) (.var 0)-(4*.var 0-3*.var 1))
      (by simp [clockPresentation,clockRelations])
    apply sub_eq_zero.mp
    simpa only [conjP,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_adj,Poly.evalC_var,
      Poly.evalC_four,Poly.evalC_three,smul_mul_assoc,one_mul] using h
  · have h := m.equations (.var 3*.var 1*.var 3-(1-.var 1))
      (by simp [clockPresentation,clockRelations])
    apply sub_eq_zero.mp
    simpa only [Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_var,Poly.evalC_one] using h
  · have h := m.equations (pc (.var 3) (conjP (.var 2) (.var 0)))
      (by simp [clockPresentation,clockRelations])
    apply sub_eq_zero.mp
    simpa only [pc,conjP,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_var,Poly.evalC_adj] using h

 theorem model_moments_zero (m : ExactModel clockPresentation A) :
    Filter.Tendsto (fun n : ℕ => (m.state.toLinearMap ((m.value 0)^n)).re)
      Filter.atTop (nhds 0) := by
  have ha : Domain.positiveContraction.HoldsC (m.value 0) := m.domains 0
  have hd := model_digits m
  apply moments_zero m.state (m.value 0) ha.1 ha.2 hd.1
  intro M
  have he : cfc (digitProduct ((List.finRange M).map Fin.val)) (m.value 0)=
      cylinder (ctranslate (m.value 2) (m.value 1)) M (fun _ => true) := by
    rw [digitProduct_cfc (m.value 0) ha.1]
    simp only [List.map_map,cylinder,ite_true]
    congr 2
    funext j
    exact (hd.2.1 j).symm
  rw [he,hd.2.2.2.2.2 M (fun _ => true)]
  have hcast : (2:ℂ)^(-(M:ℤ))=(((1/2:ℝ)^M):ℂ) := by
    norm_cast
    simp [zpow_neg,one_div,inv_pow]
  rw [hcast]
  norm_cast

 theorem model_top_projection_real (m : ExactModel clockPresentation A)
    (e : A) (he : star e=e) (hee : e*e=e) (hae : m.value 0*e=e) :
    (m.state.toLinearMap e).re=0 := by
  have ha : Domain.positiveContraction.HoldsC (m.value 0) := m.domains 0
  exact ExactTrace.top_projection_real m.state (m.value 0) ha.1 ha.2
    (model_moments_zero m) e he hee hae

 theorem model_top_projection_hermitian (m : ExactModel clockPresentation A)
    (hHermitian : ∀ a : A, IsSelfAdjoint a → (m.state.toLinearMap a).im=0)
    (e : A) (he : star e=e) (hee : e*e=e) (hae : m.value 0*e=e) :
    m.state.toLinearMap e=0 := by
  apply Complex.ext (model_top_projection_real m e he hee hae)
  exact hHermitian e he
end
end E2.ExactClock


