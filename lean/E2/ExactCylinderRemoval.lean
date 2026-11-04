import E2.ExactComputationCorner

namespace E2.ExactForcing
noncomputable section
open ExactClock
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem conjugation_fixed (x z : A) (hx : star x*x=1 ∧ x*star x=1) (hz : Commute x z) :
    shiftHom x hx 1 z=z := by
  change ctranslate x z 1=z
  simp only [ctranslate,pow_one]
  rw [hz.eq,mul_assoc,hx.2,mul_one]

theorem remove_prefix (P X : ℕ → A) (hx : ∀ j, star (X j)=X j ∧ X j*X j=1)
    (hflip : ∀ j, X j*P j*X j=1-P j)
    (htri : ∀ i j, i<j → Commute (X i) (P j)) (z : A)
    (hz : ∀ j, Commute (X j) z) (j M : ℕ) (b : ℕ → Bool)
    (h : z*clockPrefix P j M b=0) : z=0 := by
  induction M generalizing j b with
  | zero => simpa only [prefix_zero,mul_one] using h
  | succ M ih =>
    rw [prefix_succ,←mul_assoc] at h
    have hu : star (X j)*X j=1 ∧ X j*star (X j)=1 := by rw [(hx j).1]; exact ⟨(hx j).2,(hx j).2⟩
    let f := shiftHom (X j) hu 1
    have hfz : f z=z := conjugation_fixed _ _ hu (hz j)
    have hfp : f (P j)=1-P j := by
      change ctranslate (X j) (P j) 1=_
      simpa only [ctranslate,pow_one,(hx j).1] using hflip j
    have hft : f (clockPrefix P (j+1) M (dropBits b 1))=clockPrefix P (j+1) M (dropBits b 1) := by
      apply conjugation_fixed
      exact prefix_commute P (j+1) M _ _ (fun k => (htri j _ (by omega)).eq)
    have hh := remove_factor f z (P j) _ hfz hfp hft (b 0) h
    exact ih (j+1) (dropBits b 1) hh

theorem source_cross_ne {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (c e : Fin 3) (hce : c≠e) (i j : Fin 4) :
    Commute (sourceValue m (4*c.val+i.val)) (sourceValue m (4*e.val+j.val)) := by
  rcases lt_or_gt_of_ne hce with h | h
  · exact source_cross m c e h i j
  · exact (source_cross m e c h j i).symm

theorem source_shift_cross {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (c e : Fin 3) (hce : c≠e) (i j : Fin 4) (n : ℕ) :
    Commute (ctranslate (sourceValue m (4*c.val+2)) (sourceValue m (4*c.val+i.val)) n)
      (sourceValue m (4*e.val+j.val)) := by
  exact commute_shift _ _ _ n ((sourceClockModel m c).domains 2)
    (source_cross_ne m c e hce 2 j) (source_cross_ne m c e hce i j)

theorem map_finRange_range (k : ℕ) : (List.finRange k).map Fin.val=List.range k := by
  apply List.ext_getElem <;> simp

theorem prefix_range (P : ℕ → A) (M : ℕ) (b : ℕ → Bool) :
    clockPrefix P 0 M b=((List.range M).map (fun j => if b j then P j else 1-P j)).prod := by
  simp only [clockPrefix,cylinder,Nat.zero_add]
  rw [←map_finRange_range M,List.map_map]
  rfl

theorem fuel_prefix {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) :
    fuelCylinder m k=clockPrefix (ctranslate (sourceValue m 6) (sourceValue m 5)) 0 (k+1)
      (fun j => decide (j<k)) := by
  rw [prefix_range,List.prod_range_succ]
  simp only [lt_self_iff_false,decide_false,Bool.false_eq_true,ite_false]
  dsimp only [fuelCylinder]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  simp [List.mem_range.mp hj]

end
end E2.ExactForcing
