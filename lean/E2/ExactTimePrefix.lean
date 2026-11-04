import E2.ExactCylinderAlgebra

namespace E2.ExactForcing
noncomputable section
open ExactClock
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

def timePrefix {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) (b : ℕ → Bool) : A :=
  clockPrefix (ctranslate (sourceValue m 10) (sourceValue m 9)) 0 k b

theorem timePrefix_zeroCylinder {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) :
    timePrefix m k (fun _ => false)=timeZeroCylinder m k := by
  simp only [timePrefix,clockPrefix,cylinder,Nat.zero_add,Bool.false_eq_true,ite_false,timeZeroCylinder]
  congr 1
  have h : (List.finRange k).map Fin.val=List.range k := by
    apply List.ext_getElem <;> simp
  rw [←h,List.map_map]
  rfl

theorem timeStep_prefix {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (k : ℕ) (b : ℕ → Bool) :
    timeStep m (timePrefix m k b)=timePrefix m k (addBits (2^k-1) b) := by
  let cm := sourceClockModel m 2
  have hv : Domain.unitary.HoldsC (sourceValue m 13) := by
    simpa [sourceDomain] using sourceValue_domain m 13 (by omega)
  have hg : (sourceValue m 13-cm.value 3*((1-cm.value 1)+
      (cm.value 2*sourceValue m 13*star (cm.value 2))*cm.value 1))*(1-cm.value 0)=0 := by
    have hm : guardRelation (sv p 8) (sv p 9) (sv p 10) (sv p 11) (sv p 13) ∈ (sourcePresentation p).relations := by
      simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
      iterate 6 apply Or.inr
      apply Or.inl
      simp
    have he := m.equations _ hm
    simp only [guardRelation,conjP,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_add,
      Poly.evalC_adj,Poly.evalC_one,sv,Poly.evalC_var] at he
    convert he using 1 <;> rfl
  have h := model_increment cm (sourceValue m 13) hv faithful hg k (fun i => b i.val)
  rw [timeStep_apply]
  simp only [timePrefix,clockPrefix,Nat.zero_add]
  change star (sourceValue m 13)*cylinder (ctranslate (cm.value 2) (cm.value 1)) k (fun i => b i.val)*sourceValue m 13=_
  rw [h]
  congr 1
  funext j
  rw [addBits_full_prefix _ k b j.val j.isLt]
  congr 3
  have he : binaryPrefix b k=∑ i : Fin k, if b i.val then 2^i.val else 0 :=
    (Fin.sum_univ_eq_sum_range (fun i => if b i then 2^i else 0) k).symm
  rw [he]
  congr 1
  have hp : 0<2^k := by positivity
  omega

theorem timePower_prefix {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (k l : ℕ) (b : ℕ → Bool) :
    homPower (timeStep m) l (timePrefix m k b)=timePrefix m k (addBits (l*(2^k-1)) b) := by
  induction l with
  | zero => rw [homPower_zero,Nat.zero_mul,addBits_zero]
  | succ l ih =>
    rw [homPower_succ,ih,timeStep_prefix m faithful,addBits_comp]
    congr 2
    ring

theorem time_prefix_disjoint {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (faithful : ∀ z, m.state.toLinearMap (star z*z)=0 → z=0) (k l : ℕ)
    (hl : 0<l) (hlt : l<2^k) :
    homPower (timeStep m) l (timeZeroCylinder m k)*timeZeroCylinder m k=0 := by
  rw [←timePrefix_zeroCylinder,timePower_prefix m faithful]
  obtain ⟨i,hi,hbit⟩ := nonzero_prefix_bit _ k (decrement_not_zero k l hl hlt)
  change timePrefix m k (addBits (l*(2^k-1)) (fun _ => false))*timePrefix m k (fun _ => false)=0
  refine prefix_distinct_zero _ ?_ ?_ 0 k _ _ i hi ?_
  · intro j
    exact shift_projection _ _ ((sourceClockModel m 2).domains 2)
      ((sourceClockModel m 2).domains 1).2 j
  · exact fun i j => model_digit_commute (sourceClockModel m 2) i j
  · simp [hbit]

end
end E2.ExactForcing
