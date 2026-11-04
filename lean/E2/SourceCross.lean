import E2.ConditionalSource

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

theorem source_aux_clock_relation (p : CounterProgram) (n : ℕ)
    (hn : n=12 ∨ n=18 ∨ n=21 ∨ n=22) (e : Fin 2) (j : Fin 4) :
    pc (sv p n) (sv p (4*(e.val+1)+j.val))∈sourceRelations p := by
  rcases hn with rfl | rfl | rfl | rfl <;> fin_cases e
  all_goals simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
  · iterate 3 apply Or.inr
    apply Or.inl
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 4 apply Or.inr
    apply Or.inl
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 14 apply Or.inr
    apply Or.inl
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 14 apply Or.inr
    apply Or.inl
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 18 apply Or.inr
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 18 apply Or.inr
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 18 apply Or.inr
    apply commList_mem
    · simp
    · fin_cases j <;> simp
  · iterate 18 apply Or.inr
    apply commList_mem
    · simp
    · fin_cases j <;> simp

theorem source_aux_clock_base {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (n : ℕ)
    (hn : n=12 ∨ n=18 ∨ n=21 ∨ n=22) (e : Fin 2) (j : Fin 4) :
    weighted m.state (comm (sourceAt m n) (sourceAt m (4*(e.val+1)+j.val)))≤δ := by
  have h := m.defects _ (source_aux_clock_relation p n hn e j)
  simpa [sourceAt,pc,comm,Companion.Analytic.comm] using h

theorem source_conditional_variable_norm {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (n : ℕ) (hn : n=18 ∨ n=21 ∨ n=22) :
    ‖sourceAt m n‖≤1 := by
  rcases hn with rfl | rfl | rfl
  · exact projection_norm_le (by simpa [sourceDomain] using sourceAt_domain m 18 (by omega))
  · exact projection_norm_le (by simpa [sourceDomain] using sourceAt_domain m 21 (by omega))
  · exact (unitary_norm m.positive_dimension (reflection_unitary _
      (by simpa [sourceDomain] using sourceAt_domain m 22 (by omega)))).le

/-- Item (v): raw conditional digits/flips against fuel or time. The entire
estimate is cubic in the two word depths and has no spectral depth factor. -/
theorem source_conditional_clock_words {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (hδ : 0≤δ) (n : ℕ) (hn : n=18 ∨ n=21 ∨ n=22)
    (e : Fin 2) (l : Fin 4) (i j : ℕ) :
    weighted m.state (comm (translate (sourceAt m 12) (sourceAt m n) i)
      (translate (sourceAt m (4*(e.val+1)+2)) (sourceAt m (4*(e.val+1)+l.val)) j))≤
      5*(2*(i:ℝ)+1)*(2*(j:ℝ)+1)*(2*i+2*j+3)*δ := by
  let c : Fin 3 := ⟨e.val+1,by have := e.isLt; omega⟩
  have hV : Domain.unitary.Holds (sourceAt m 12) := by simpa [sourceDomain] using sourceAt_domain m 12 (by omega)
  have hc := sourceClock_valid m c
  have hU : Domain.unitary.Holds (sourceAt m (4*(e.val+1)+2)) := hc.2.2.1
  have hnZ : ‖sourceAt m (4*(e.val+1)+l.val)‖≤1 := source_clock_variable_norm m c l
  apply translated_word_commutator m.state δ _ _ _ _ hδ hV hU (source_conditional_variable_norm m n hn) hnZ
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact sourceAt_state m _
  · exact source_aux_clock_base m 12 (Or.inl rfl) e 2
  · exact source_aux_clock_base m 12 (Or.inl rfl) e l
  · exact source_aux_clock_base m n (Or.inr hn) e 2
  · exact source_aux_clock_base m n (Or.inr hn) e l

theorem source_conditional_address_relation (p : CounterProgram) (n : ℕ) (hn : n=18 ∨ n=21 ∨ n=22) :
    pc (sv p n) (sv p 0)∈sourceRelations p := by
  rcases hn with rfl | rfl | rfl
  all_goals simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
  · iterate 14 apply Or.inr
    apply Or.inl
    exact commList_mem _ _ _ _ (by simp) (by simp)
  · iterate 18 apply Or.inr
    exact commList_mem _ _ _ _ (by simp) (by simp)
  · iterate 18 apply Or.inr
    exact commList_mem _ _ _ _ (by simp) (by simp)

/-- Item (iv): the address estimate on the actual source, obtained from the
already-proved carry theorem with no iteration of digit Lipschitz constants. -/
theorem source_conditional_address_words : ∃ C : ℝ, 0<C ∧
    ∀ (p : CounterProgram) (d : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ), 0≤δ →
      ∀ n : ℕ, n=18 ∨ n=21 ∨ n=22 → ∀ i j : ℕ,
        weighted m.state (comm (translate (sourceAt m 12) (sourceAt m n) i)
          (rawDigit (sourceClock m 0) j))≤C*(i+1)*4^j*δ := by
  obtain ⟨C,hC,hrepair⟩ := carry_translation
  refine ⟨C,hC,?_⟩
  intro p d δ m hδ n hn i j
  obtain ⟨r⟩ := hrepair d m.state δ (sourceClock m 0) (sourceAt m 12) (sourceAt m 14)
    hδ (source_address_approx m)
  apply r.joint_address i j (sourceAt m n) (source_conditional_variable_norm m n hn)
  · have h := m.defects _ (source_conditional_address_relation p n hn)
    simpa [sourceAt,sourceClock,pc,comm,Companion.Analytic.comm] using h
  · exact sourceAt_state m _

end
end E2
