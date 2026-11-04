import E2.SourceJointSlots
import E2.JointScale

namespace E2
noncomputable section
open scoped Matrix.Norms.L2Operator

/-- All conditional variables, including Y, against every compulsory raw digit.
Address uses carry routing; fuel/time use raw words. -/
theorem source_conditional_compulsory_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : CounterProgram) (d M : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ),
      0 ≤ δ → ∀ n : ℕ, n=18 ∨ n=21 ∨ n=22 → ∀ i j : Fin M, ∀ c : Fin 3,
      weighted m.state (comm (translate (sourceAt m 12) (sourceAt m n) i.val)
        (rawDigit (sourceClock m c) j.val)) ≤ rawClockScale C M δ := by
  obtain ⟨K,hK,haddr⟩ := source_conditional_address_words
  let L := K+1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hKL : K ≤ L := by dsimp [L]; linarith
  refine ⟨100*L,by linarith,?_⟩
  intro p d M δ m hδ n hn i j c
  let E := rawClockScale L M δ
  have hE : 0 ≤ E := by unfold E rawClockScale; positivity
  have hs : rawClockScale (100*L) M δ=100*E := by dsimp [E,rawClockScale]; ring
  rw [hs]
  fin_cases c
  · have h := haddr p d δ m hδ n hn i.val j.val
    have hb := joint_address_scale K L δ M i.val j.val (le_of_lt hK) hKL hL hδ (by omega) (by omega)
    exact h.trans (by linarith)
  · have h := source_conditional_clock_words m hδ n hn 0 1 i.val j.val
    have hb := joint_word_scale L δ M i.val j.val hL hδ (by omega) (by omega)
    have hh : weighted m.state (comm (translate (sourceAt m 12) (sourceAt m n) i.val)
        (rawDigit (sourceClock m 1) j.val)) ≤ 5*(2*(i.val:ℝ)+1)*(2*(j.val:ℝ)+1)*(2*i.val+2*j.val+3)*δ := by simpa [rawDigit,sourceClock] using h
    exact hh.trans (by linarith)
  · have h := source_conditional_clock_words m hδ n hn 1 1 i.val j.val
    have hb := joint_word_scale L δ M i.val j.val hL hδ (by omega) (by omega)
    have hh : weighted m.state (comm (translate (sourceAt m 12) (sourceAt m n) i.val)
        (rawDigit (sourceClock m 2) j.val)) ≤ 5*(2*(i.val:ℝ)+1)*(2*(j.val:ℝ)+1)*(2*i.val+2*j.val+3)*δ := by simpa [rawDigit,sourceClock] using h
    exact hh.trans (by linarith)

end
end E2
