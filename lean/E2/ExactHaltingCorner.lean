import E2.ExactCylinderRemoval

namespace E2.ExactForcing
noncomputable section
open ExactClock
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem flag_corner_support {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e k : ℕ) :
    (1-sourceValue m 18)*computationCorner m e k=computationCorner m e k := by
  let F := sourceValue m 18
  have hp : IsIdempotentElem F := (show Domain.projection.HoldsC F from
    by simpa [sourceDomain] using sourceValue_domain m 18 (by omega)).2
  have hFK := fuel_commute m F (source_hlf_comm m 18 (by simp) (sv p 4) (by simp)) k
  have hFD := time_commute m F (source_hlf_comm m 18 (by simp) (sv p 8) (by simp)) k
  have hFB := address_commute m F (source_hlf_comm m 18 (by simp) (sv p 0) (by simp)) e
  have hc : Commute (1-F) (fuelCylinder m k*timeZeroCylinder m k*addressCylinder m e) :=
    (Commute.one_left _).sub_left ((hFK.mul_right hFD).mul_right hFB)
  change (1-F)*(fuelCylinder m k*timeZeroCylinder m k*(addressCylinder m e*(1-F)))=_
  rw [←mul_assoc (fuelCylinder m k*timeZeroCylinder m k),←mul_assoc,hc.eq,mul_assoc,hp.one_sub.eq]
  simp only [mul_assoc,computationCorner,F]

theorem halting_corner_zero {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (e h k : ℕ) (hh : h<2^k)
    (hhalt : ((p.step)^[h] (p.initial e)).control=p.halt) : computationCorner m e k=0 := by
  have hq := (corner_finite_computation m faithful e k h hh).2 p.halt
  simp only [hhalt,ite_true] at hq
  have hm : (1-sv p 18)*sq p p.halt ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 12 apply Or.inr
    apply Or.inl
    simp
  have he : (1-sourceValue m 18)*(sq p p.halt).evalC m.value=0 := by
    simpa only [Poly.evalC_mul,Poly.evalC_sub,Poly.evalC_one,sv,Poly.evalC_var,sourceValue] using m.equations _ hm
  have hf := congrArg (homPower (timeStep m) h) he
  rw [map_mul,map_sub,map_one,map_zero,timePower_fixed m _
    (source_hlf_comm m 18 (by simp) (sv p 13) (by simp)).symm] at hf
  calc
    computationCorner m e k=(1-sourceValue m 18)*computationCorner m e k := (flag_corner_support m e k).symm
    _=(1-sourceValue m 18)*(homPower (timeStep m) h ((sq p p.halt).evalC m.value)*computationCorner m e k) := by rw [hq]
    _=0 := by rw [←mul_assoc,hf,zero_mul]

theorem flag_address_flip_comm {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (c : Fin 3) (hc : c≠0) (j e : ℕ) :
    Commute (ctranslate (sourceValue m (4*c.val+2)) (sourceValue m (4*c.val+3)) j)
      (addressCylinder m e*(1-sourceValue m 18)) := by
  have hB := address_commute m _ (source_shift_cross m c 0 hc 3 0 j) e
  have hT : Commute (sourceValue m (4*c.val+2)) (sourceValue m 18) := by
    apply Commute.symm
    apply source_hlf_comm m 18 (by simp) (sv p (4*c.val+2))
    fin_cases c <;> simp_all
  have hX : Commute (sourceValue m (4*c.val+3)) (sourceValue m 18) := by
    apply Commute.symm
    apply source_hlf_comm m 18 (by simp) (sv p (4*c.val+3))
    fin_cases c <;> simp_all
  have hF := commute_shift _ _ _ j ((sourceClockModel m c).domains 2) hT hX
  exact hB.mul_right ((Commute.one_right _).sub_right hF)

theorem halting_address_support {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (e h : ℕ)
    (hhalt : ((p.step)^[h] (p.initial e)).control=p.halt) :
    addressCylinder m e*(1-sourceValue m 18)=0 := by
  let z := addressCylinder m e*(1-sourceValue m 18)
  let K := fuelCylinder m h
  let D := timeZeroCylinder m h
  have hK : Commute z K := by
    apply fuel_commute
    apply Commute.mul_left
    · exact (address_commute m _ (source_cross m 0 1 (by decide) 0 0).symm e).symm
    · exact (Commute.one_left _).sub_left (source_hlf_comm m 18 (by simp) (sv p 4) (by simp))
  have hD : Commute z D := by
    apply time_commute
    apply Commute.mul_left
    · exact (address_commute m _ (source_cross m 0 2 (by decide) 0 0).symm e).symm
    · exact (Commute.one_left _).sub_left (source_hlf_comm m 18 (by simp) (sv p 8) (by simp))
  have hKD : Commute K D := by
    apply time_commute
    exact (fuel_commute m _ (source_cross m 1 2 (by decide) 0 0).symm h).symm
  have hz : (z*D)*K=0 := by
    calc
      (z*D)*K=K*D*z := by
        rw [mul_assoc,hKD.symm.eq,←mul_assoc,hK.eq,mul_assoc,hD.eq,←mul_assoc]
      _=0 := halting_corner_zero m faithful e h h h.lt_two_pow_self hhalt
  have hzD : z*D=0 := by
    dsimp only [K] at hz
    rw [fuel_prefix] at hz
    apply remove_prefix _ (ctranslate (sourceValue m 6) (sourceValue m 7))
      (fun j => shift_reflection _ _ ((sourceClockModel m 1).domains 2) ((sourceClockModel m 1).domains 3) j)
      (model_digits (sourceClockModel m 1)).2.2.2.1
      (fun i j hij => (model_digits (sourceClockModel m 1)).2.2.2.2.1 i j hij)
      (z*D) ?_ 0 (h+1) _ hz
    intro j
    apply Commute.mul_right
    · exact flag_address_flip_comm m 1 (by decide) j e
    · exact time_commute m _ (source_shift_cross m 1 2 (by decide) 3 0 j) h
  dsimp only [D] at hzD
  rw [←timePrefix_zeroCylinder] at hzD
  exact remove_prefix _ (ctranslate (sourceValue m 10) (sourceValue m 11))
    (fun j => shift_reflection _ _ ((sourceClockModel m 2).domains 2) ((sourceClockModel m 2).domains 3) j)
    (model_digits (sourceClockModel m 2)).2.2.2.1
    (fun i j hij => (model_digits (sourceClockModel m 2)).2.2.2.2.1 i j hij)
    z (fun j => flag_address_flip_comm m 2 (by decide) j e) 0 h _ hzD

end
end E2.ExactForcing
