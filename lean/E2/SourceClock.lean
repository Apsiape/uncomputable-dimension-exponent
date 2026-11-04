import E2.Carry
import E2.PolyEval
import E2.TranslatedWords

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 100000

def sourceAt {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : ℕ) : Mat d := Poly.eval m.value (sv p i)

def sourceClock {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) : ClockData d :=
  ⟨sourceAt m (4*c.val),sourceAt m (4*c.val+1),sourceAt m (4*c.val+2),sourceAt m (4*c.val+3)⟩

theorem sourceAt_domain {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : ℕ) (hi : i<23) :
    (sourceDomain p ⟨i,by unfold sourceSize; omega⟩).Holds (sourceAt m i) := by
  have h := m.domains ⟨i%sourceSize p,Nat.mod_lt _ (by unfold sourceSize; omega)⟩
  simpa only [sourcePresentation,sourceAt,sv,Poly.eval,Nat.mod_eq_of_lt (show i<sourceSize p by unfold sourceSize; omega)] using h

theorem sourceAt_state {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : ℕ) : hs (comm (sourceAt m i) m.state.xi)≤δ :=
  m.state_commutators _

theorem sourceClock_valid {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) : (sourceClock m c).Valid := by
  fin_cases c
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 0 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 1 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 2 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 3 (by omega)
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 4 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 5 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 6 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 7 (by omega)
  · refine ⟨?_,?_,?_,?_⟩
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 8 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 9 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 10 (by omega)
    · simpa [sourceDomain,sourceClock] using sourceAt_domain m 11 (by omega)

theorem source_clock_relation {p : CounterProgram} (c : Fin 3) (r : SourcePoly p)
    (hr : r∈clockRelations (sv p (4*c.val)) (sv p (4*c.val+1))
      (sv p (4*c.val+2)) (sv p (4*c.val+3))) : r∈sourceRelations p := by
  fin_cases c
  · change r∈clockRelations (sv p 0) (sv p 1) (sv p 2) (sv p 3) at hr
    simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    exact Or.inl hr
  · change r∈clockRelations (sv p 4) (sv p 5) (sv p 6) (sv p 7) at hr
    simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    exact Or.inr (Or.inl hr)
  · change r∈clockRelations (sv p 8) (sv p 9) (sv p 10) (sv p 11) at hr
    simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    exact Or.inr (Or.inr (Or.inl hr))

theorem sourceClock_approx {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) : ClockApprox m.state δ (sourceClock m c) := by
  refine ⟨sourceClock_valid m c,?_,?_⟩
  · intro r hr
    simp only [ClockData.defects,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · have h := m.defects (pc (sv p (4*c.val)) (sv p (4*c.val+1)))
        (source_clock_relation c _ (by simp [clockRelations]))
      simpa [Poly.eval,pc,sourceAt,sourceClock,comm,Companion.Analytic.comm,
        Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul] using h
    · have h := m.defects (conjP (sv p (4*c.val+2)) (sv p (4*c.val))-
          (4*sv p (4*c.val)-3*sv p (4*c.val+1)))
        (source_clock_relation c _ (by simp [clockRelations]))
      simpa [Poly.eval,conjP,sourceAt,sourceClock,Matrix.smul_mul,Matrix.mul_smul] using h
    · have h := m.defects (sv p (4*c.val+3)*sv p (4*c.val+1)*sv p (4*c.val+3)-(1-sv p (4*c.val+1)))
        (source_clock_relation c _ (by simp [clockRelations]))
      simpa [Poly.eval,sourceAt,sourceClock,Matrix.smul_mul,Matrix.mul_smul] using h
    · have h := m.defects (pc (sv p (4*c.val+3)) (conjP (sv p (4*c.val+2)) (sv p (4*c.val))))
        (source_clock_relation c _ (by simp [clockRelations]))
      simpa [Poly.eval,pc,conjP,sourceAt,sourceClock,comm,Companion.Analytic.comm,
        Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul] using h
  · intro X hX
    simp only [ClockData.variables,List.mem_cons,List.not_mem_nil,or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> exact sourceAt_state m _

def addressRelations (p : CounterProgram) : List (SourcePoly p) :=
  [sv p 14-((1-sv p 1)+.const (1/4)*sv p 1*conjP (sv p 2) (sv p 14)),
   pc (sv p 1) (conjP (sv p 2) (sv p 14)),pc (sv p 14) (sv p 0),
   conjP (sv p 12).adj (sv p 0)-(sv p 0-1+.const (7/4)*sv p 14)]

theorem source_address_relation (p : CounterProgram) (r : SourcePoly p) (hr : r∈addressRelations p) :
    r∈sourceRelations p := by
  simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
  apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
  simp only [addressRelations,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- The actual source supplies the unguarded address/carry hypotheses on its
original state; no guard-removal estimate or program-specific constant is used. -/
theorem source_address_approx {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) :
    AddressApprox m.state δ (sourceClock m 0) (sourceAt m 12) (sourceAt m 14) := by
  refine ⟨sourceClock_approx m 0,?_,?_,?_,?_,?_,?_,sourceAt_state m 12,sourceAt_state m 14⟩
  · simpa [sourceDomain] using sourceAt_domain m 12 (by omega)
  · simpa [sourceDomain] using sourceAt_domain m 14 (by omega)
  · have h := m.defects _ (source_address_relation p _ (show
        sv p 14-((1-sv p 1)+.const (1/4)*sv p 1*conjP (sv p 2) (sv p 14))∈addressRelations p by simp [addressRelations]))
    simpa [sourceAt,sourceClock,conjP,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc] using h
  · have h := m.defects (pc (sv p 1) (conjP (sv p 2) (sv p 14)))
        (source_address_relation p _ (by simp [addressRelations]))
    simpa [sourceAt,sourceClock,conjP,pc,comm,Companion.Analytic.comm] using h
  · have h := m.defects (pc (sv p 14) (sv p 0))
        (source_address_relation p _ (by simp [addressRelations]))
    simpa [sourceAt,sourceClock,pc,comm,Companion.Analytic.comm] using h
  · have h := m.defects (conjP (sv p 12).adj (sv p 0)-(sv p 0-1+.const (7/4)*sv p 14))
        (source_address_relation p _ (by simp [addressRelations]))
    simpa [sourceAt,sourceClock,conjP,Matrix.smul_mul,Matrix.mul_smul] using h

theorem commList_mem {ι : Type*} (xs ys : List (Poly ι)) (x y : Poly ι)
    (hx : x∈xs) (hy : y∈ys) : pc x y∈commList xs ys := by
  exact List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩

theorem source_clock_cross_relation (p : CounterProgram) (c e : Fin 3) (hce : c<e) (i j : Fin 4) :
    pc (sv p (4*c.val+i.val)) (sv p (4*e.val+j.val))∈sourceRelations p := by
  change c.val<e.val at hce
  fin_cases c <;> fin_cases e <;> norm_num at hce
  all_goals simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
  · iterate 3 apply Or.inr
    apply Or.inl
    apply commList_mem
    · fin_cases i <;> simp
    · fin_cases j <;> simp
  · iterate 4 apply Or.inr
    apply Or.inl
    apply commList_mem
    · fin_cases i <;> simp
    · fin_cases j <;> simp
  · iterate 5 apply Or.inr
    apply Or.inl
    apply commList_mem
    · fin_cases i <;> simp
    · fin_cases j <;> simp

theorem source_clock_cross_base {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c e : Fin 3) (hce : c≠e) (i j : Fin 4) :
    weighted m.state (comm (sourceAt m (4*c.val+i.val)) (sourceAt m (4*e.val+j.val)))≤δ := by
  wlog h : c<e generalizing c e i j
  · have hrev : e<c := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hce)
    rw [weighted_comm_symm]
    exact this e c (Ne.symm hce) j i hrev
  have h := m.defects _ (source_clock_cross_relation p c e h i j)
  simpa [sourceAt,pc,comm,Companion.Analytic.comm] using h

theorem source_clock_variable_norm {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (c : Fin 3) (i : Fin 4) :
    ‖sourceAt m (4*c.val+i.val)‖≤1 := by
  have hc := sourceClock_valid m c
  fin_cases i
  · simpa [sourceClock] using positive_contraction_norm hc.1
  · simpa [sourceClock] using projection_norm_le hc.2.1
  · simpa [sourceClock] using (unitary_norm m.positive_dimension hc.2.2.1).le
  · simpa [sourceClock] using
      (unitary_norm m.positive_dimension (reflection_unitary _ hc.2.2.2)).le

/-- The cubic raw-word bound for every pair of different compulsory clocks.
It applies both to digit/digit and flip/digit pairs before outcome complements. -/
theorem source_clock_cross_words {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (hδ : 0≤δ) (c e : Fin 3) (hce : c≠e)
    (k l : Fin 4) (i j : ℕ) :
    weighted m.state (comm
      (translate (sourceClock m c).T (sourceAt m (4*c.val+k.val)) i)
      (translate (sourceClock m e).T (sourceAt m (4*e.val+l.val)) j))≤
      5*(2*(i:ℝ)+1)*(2*(j:ℝ)+1)*(2*i+2*j+3)*δ := by
  apply translated_word_commutator m.state δ _ _ _ _ hδ
    (sourceClock_valid m c).2.2.1 (sourceClock_valid m e).2.2.1
    (source_clock_variable_norm m c k) (source_clock_variable_norm m e l)
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact source_clock_cross_base m c e hce 2 2
  · exact source_clock_cross_base m c e hce 2 l
  · exact source_clock_cross_base m c e hce k 2
  · exact source_clock_cross_base m c e hce k l

end
end E2
