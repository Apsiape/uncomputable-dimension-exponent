import E2.ExactAddressMass

namespace E2.ExactForcing
noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem sum_orthogonal_projections {ι : Type*} (P : ι → A) (s : Finset ι)
    (hp : ∀ i, IsStarProjection (P i)) (ho : ∀ i j, i≠j → P i*P j=0) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsStarProjection.zero A
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i).add ih
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    exact ho i j (by intro he; subst j; exact hi hj)

theorem finite_flag_bound {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0)
    (hp : RecognizesK p) (s : Finset ℕ) (hs : ∀ e ∈ s, e ∈ haltingSet) :
    (∑ e ∈ s, haltingWeight e)≤(m.state.toLinearMap (sourceValue m 18)).re := by
  have hF : IsStarProjection (sourceValue m 18) := by
    have hd : Domain.projection.HoldsC (sourceValue m 18) := by
      simpa [sourceDomain] using sourceValue_domain m 18 (by omega)
    exact ⟨hd.2,hd.1⟩
  let S := ∑ e ∈ s, addressCylinder m e
  have hS : IsStarProjection S := sum_orthogonal_projections _ s (address_projection m) (address_orthogonal m)
  have hSF : S*sourceValue m 18=S := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    obtain ⟨h,hh⟩ := (hp e).mpr (hs e he)
    have hc := halting_address_support m faithful e h hh
    exact (sub_eq_zero.mp (by simpa only [mul_sub,mul_one] using hc)).symm
  have hd := hS.sub_of_mul_eq_left hF hSF
  have hpos := m.state.positive (sourceValue m 18-S)
  rw [hd.isSelfAdjoint.star_eq,hd.isIdempotentElem.eq,map_sub,Complex.sub_re] at hpos
  have hm : (m.state.toLinearMap S).re=∑ e ∈ s, haltingWeight e := by
    simp only [S,map_sum,Complex.re_sum,address_mass]
    apply Finset.sum_congr rfl
    intro e he
    simp only [haltingWeight]
    have hc : (4:ℂ)^(-(e+1:ℤ))=Complex.ofReal ((4:ℝ)^(-(e+1:ℤ))) := by
      simpa using (map_zpow₀ Complex.ofRealHom (4:ℝ) (-(e+1:ℤ))).symm
    rw [hc,Complex.ofReal_re]
  rw [hm] at hpos
  linarith

theorem faithful_flag_density {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (hp : RecognizesK p) :
    thetaK≤(m.state.toLinearMap (sourceValue m 18)).re := by
  classical
  unfold thetaK
  apply Real.tsum_le_of_sum_le
  · intro e
    change 0 ≤ (if e∈haltingSet then haltingWeight e else 0)
    simp only [haltingWeight]
    split_ifs <;> positivity
  · intro s
    have hh := finite_flag_bound m faithful hp (s.filter (fun e => e∈haltingSet))
      (fun e he => (Finset.mem_filter.mp he).2)
    simpa only [Finset.sum_filter] using hh

theorem model_flag_density (p : CounterProgram) (hp : RecognizesK p)
    (m : ExactModel (sourcePresentation p) A) : thetaK≤(m.state.toLinearMap (sourceValue m 18)).re := by
  have h := faithful_flag_density (ExactTrace.faithfulModel m)
    (ExactTrace.faithfulModel_faithful m) hp
  have hsa : IsSelfAdjoint ((sv p 18).evalC m.value) := by
    exact (show Domain.projection.HoldsC (sourceValue m 18) from
      by simpa [sourceDomain] using sourceValue_domain m 18 (by omega)).1
  have he := ExactTrace.faithfulModel_preserves m (sv p 18) hsa
  simpa only [sv,Poly.evalC_var,sourceValue] using he ▸ h

end
end E2.ExactForcing
