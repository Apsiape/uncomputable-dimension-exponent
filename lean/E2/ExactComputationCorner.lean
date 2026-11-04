import E2.ExactSourceCommutation

namespace E2.ExactForcing
noncomputable section
open ExactClock
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem model_digit_projection (cm : ExactModel clockPresentation A) (j : ℕ) :
    IsStarProjection (ctranslate (cm.value 2) (cm.value 1) j) := by
  have ht : Domain.unitary.HoldsC (cm.value 2) := cm.domains 2
  have hp : Domain.projection.HoldsC (cm.value 1) := cm.domains 1
  exact ⟨shift_projection _ _ ht hp.2 j,by change star (ctranslate (cm.value 2) (cm.value 1) j)=_; rw [shift_star,hp.1]⟩

theorem timeZero_projection {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) :
    IsStarProjection (timeZeroCylinder m k) := by
  rw [←timePrefix_zeroCylinder]
  exact prefix_projection _ (model_digit_projection (sourceClockModel m 2))
    (model_digit_commute (sourceClockModel m 2)) 0 k _

theorem fuel_timeStep_fixed {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k l : ℕ) :
    homPower (timeStep m) l (fuelCylinder m k)=fuelCylinder m k := by
  apply timePower_fixed
  apply fuel_commute
  have hm : pc (sv p 4) (sv p 13) ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 5 apply Or.inr
    apply Or.inl
    exact commList_mem _ _ _ _ (by simp) (by simp)
  have he := m.equations _ hm
  have hc : Commute (sourceValue m 4) (sourceValue m 13) :=
    sub_eq_zero.mp (by simpa only [pc,Poly.evalC_sub,Poly.evalC_mul,sv,Poly.evalC_var,sourceValue] using he)
  exact hc.symm

theorem reset_evolution {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (k l : ℕ) (W : A) (hlt : l<2^k) :
    homPower (timeStep m) l (sourceValue m 17)*(fuelCylinder m k*timeZeroCylinder m k*W)=
      if l=0 then fuelCylinder m k*timeZeroCylinder m k*W else 0 := by
  let f := homPower (timeStep m) l
  have hzc : Commute (sourceValue m 17) (fuelCylinder m k) :=
    fuel_commute m _ (source_workspace_external_comm m (sv p 17) (by simp) (sv p 4) (by simp)) k
  have hzc' : Commute (f (sourceValue m 17)) (fuelCylinder m k) := by
    change f (sourceValue m 17)*fuelCylinder m k=fuelCylinder m k*f (sourceValue m 17)
    have hh := congrArg f hzc.eq
    simpa only [f,map_mul,fuel_timeStep_fixed] using hh
  have hr : fuelCylinder m k*f (sourceValue m 17)=fuelCylinder m k*f (timeZeroCylinder m k) := by
    have hh := congrArg f (reset_initialization m k)
    simpa only [f,map_mul,fuel_timeStep_fixed] using hh
  calc
    _ = fuelCylinder m k*(f (sourceValue m 17)*timeZeroCylinder m k)*W := by
      change f (sourceValue m 17)*(fuelCylinder m k*timeZeroCylinder m k*W)=_
      rw [←mul_assoc,←mul_assoc,hzc'.eq]
      simp only [mul_assoc]
    _ = fuelCylinder m k*(f (timeZeroCylinder m k)*timeZeroCylinder m k)*W := by
      rw [←mul_assoc (fuelCylinder m k),hr]
      simp only [mul_assoc]
    _ = _ := by
      by_cases hl : l=0
      · subst l
        simp only [ite_true,f,homPower_zero,(timeZero_projection m k).isIdempotentElem.eq]
      · rw [time_prefix_disjoint m faithful k l (by omega) hlt, mul_zero,zero_mul,if_neg hl]

def computationCorner {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e k : ℕ) : A :=
  fuelCylinder m k*timeZeroCylinder m k*(addressCylinder m e*(1-sourceValue m 18))

theorem corner_address_action {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (n : ℕ) (hn : n ∈ [15,16,18]) (e k : ℕ) (a : ℂ)
    (he : addressCylinder m e*sourceValue m n=a • addressCylinder m e) :
    sourceValue m n*computationCorner m e k=a • computationCorner m e k := by
  have hA := source_hlf_comm m n hn (sv p 0) (by simp)
  have hF := fuel_commute m _ (source_hlf_comm m n hn (sv p 4) (by simp)) k
  have hT := time_commute m _ (source_hlf_comm m n hn (sv p 8) (by simp)) k
  have hE := address_commute m _ hA e
  simp only [computationCorner]
  calc
    _ = fuelCylinder m k*timeZeroCylinder m k*(sourceValue m n*addressCylinder m e)*(1-sourceValue m 18) := by
      rw [←mul_assoc,←mul_assoc,(hF.mul_right hT).eq]
      simp only [mul_assoc]
    _ = a • (fuelCylinder m k*timeZeroCylinder m k*(addressCylinder m e*(1-sourceValue m 18))) := by
      rw [hE.eq,he,mul_smul_comm,smul_mul_assoc]
      simp only [mul_assoc]

theorem corner_finite_computation {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (e k h : ℕ) (hh : h<2^k) :
    (∀ i, homPower (timeStep m) h ((sr p i).evalC m.value)*computationCorner m e k=
      counterCode (((p.step)^[h] (p.initial e)).counter i) • computationCorner m e k) ∧
    (∀ q, homPower (timeStep m) h ((sq p q).evalC m.value)*computationCorner m e k=
      if q=((p.step)^[h] (p.initial e)).control then computationCorner m e k else 0) := by
  apply finite_program_iteration m e h (computationCorner m e k) ?_ ?_ ?_ ?_ h (le_refl h)
  · have hz := reset_evolution m faithful k 0 (addressCylinder m e*(1-sourceValue m 18)) (by positivity)
    simpa only [homPower_zero,ite_true,computationCorner] using hz
  · intro l hl hlh
    simpa only [if_neg (Nat.ne_of_gt hl),computationCorner] using
      reset_evolution m faithful k l (addressCylinder m e*(1-sourceValue m 18)) (by omega)
  · intro l hl
    rw [timePower_fixed m _ (source_hlf_comm m 15 (by simp) (sv p 13) (by simp)).symm]
    have ha := corner_address_action m 15 (by simp) e k 1 (by simpa using (address_initialization m).1 e)
    simpa using ha
  · intro l hl
    rw [timePower_fixed m _ (source_hlf_comm m 16 (by simp) (sv p 13) (by simp)).symm]
    exact corner_address_action m 16 (by simp) e k (counterCode e) ((address_initialization m).2 e)

end
end E2.ExactForcing
