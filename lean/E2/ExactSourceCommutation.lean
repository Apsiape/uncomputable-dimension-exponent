import E2.ExactTimePrefix

namespace E2.ExactForcing
noncomputable section
open ExactClock
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem clock_digit_commute (cm : ExactModel clockPresentation A) (x : A)
    (hx : Commute x (cm.value 0)) (j : ℕ) :
    Commute x (ctranslate (cm.value 2) (cm.value 1) j) := by
  rw [(model_digits cm).2.1 j]
  exact (hx.symm.cfc_real (digitAt j)).symm

theorem source_hlf_comm {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (n : ℕ) (hn : n ∈ [15,16,18]) (r : SourcePoly p)
    (hr : r ∈ [sv p 0,sv p 4,sv p 5,sv p 6,sv p 7,sv p 8,sv p 9,sv p 10,sv p 11,sv p 13]) :
    Commute (sourceValue m n) (r.evalC m.value) := by
  have hm : pc (sv p n) r ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 14 apply Or.inr
    apply Or.inl
    apply commList_mem
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simp
    · exact hr
  exact sub_eq_zero.mp (by simpa only [pc,Poly.evalC_sub,Poly.evalC_mul,sv,Poly.evalC_var,sourceValue] using m.equations _ hm)

theorem source_workspace_external_comm {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (w : SourcePoly p) (hw : w ∈ sv p 17 :: sourceWork p) (r : SourcePoly p)
    (hr : r ∈ [sv p 0,sv p 4,sv p 8,sv p 15,sv p 16,sv p 18]) :
    Commute (w.evalC m.value) (r.evalC m.value) := by
  have hm : pc w r ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 16 apply Or.inr
    apply Or.inl
    exact commList_mem _ _ _ _ hw hr
  exact sub_eq_zero.mp (by simpa only [pc,Poly.evalC_sub,Poly.evalC_mul] using m.equations _ hm)

theorem address_commute {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (x : A) (hx : Commute x (sourceValue m 0)) (e : ℕ) : Commute x (addressCylinder m e) := by
  let v := sourceValue m
  have ht : star (v 2)*v 2=1 ∧ v 2*star (v 2)=1 := (sourceClockModel m 0).domains 2
  have hd (j : ℕ) : Commute x (ctranslate (v 2) (v 1) j) := clock_digit_commute (sourceClockModel m 0) x hx j
  have ha (j : ℕ) : Commute x (ctranslate (v 2) ((1-v 1)*(1-ctranslate (v 2) (v 1) 1)) j) := by
    rw [shift_mul _ _ _ ht,shift_sub,shift_sub,shift_one _ ht,shift_shift]
    exact ((Commute.one_right _).sub_right (hd j)).mul_right ((Commute.one_right _).sub_right (hd _))
  have hb (j : ℕ) : Commute x (ctranslate (v 2) (v 1*(1-ctranslate (v 2) (v 1) 1)) j) := by
    rw [shift_mul _ _ _ ht,shift_sub,shift_one _ ht,shift_shift]
    exact (hd j).mul_right ((Commute.one_right _).sub_right (hd _))
  apply Commute.mul_right _ (hb (2*e))
  apply Commute.list_prod_right
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact ha (2*j)

theorem fuel_commute {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (x : A) (hx : Commute x (sourceValue m 4)) (k : ℕ) : Commute x (fuelCylinder m k) := by
  have hd (j : ℕ) := clock_digit_commute (sourceClockModel m 1) x hx j
  apply Commute.mul_right _ ((Commute.one_right _).sub_right (hd k))
  apply Commute.list_prod_right
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact hd j

theorem time_commute {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (x : A) (hx : Commute x (sourceValue m 8)) (k : ℕ) : Commute x (timeZeroCylinder m k) := by
  have hd (j : ℕ) := clock_digit_commute (sourceClockModel m 2) x hx j
  apply Commute.list_prod_right
  intro z hz
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hz
  exact (Commute.one_right _).sub_right (hd j)

theorem timePower_fixed {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (x : A) (hx : Commute (sourceValue m 13) x) (l : ℕ) : homPower (timeStep m) l x=x := by
  have hu : Domain.unitary.HoldsC (sourceValue m 13) := by
    simpa [sourceDomain] using sourceValue_domain m 13 (by omega)
  have hstep : timeStep m x=x := by
    rw [timeStep_apply,mul_assoc,←hx.eq,←mul_assoc,hu.1,one_mul]
  induction l with
  | zero => rfl
  | succ l ih => rw [homPower_succ,ih,hstep]

end
end E2.ExactForcing
