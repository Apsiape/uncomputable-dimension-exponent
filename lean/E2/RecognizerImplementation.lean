import E2.RecognizerTM2Simulation
import E2.RecognizerInput
import E2.RecognizerUniversal

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2 Function CounterStack Relation StateTransition

noncomputable def compiledRecognizer (c : ToPartrec.Code) : CounterProgram :=
  let S := codeSupp c .halt
  let hs : Closed S := (tr_supports c .halt).2
  let entry := trNormal c .halt
  let he : entry ∈ S := (tr_supports c .halt).1
  CounterFlow.program (by decide : 0 < 6)
    (table (by decide : 0 < 5) (machine S hs entry he)) (.run (.inl 0))

theorem low_input (S : Finset Λ') (q : Labels S) (e : ℕ) :
    CounterFlow.input (r := 6) (Ctrl 5 5 (Labels S)) (.run q) e =
      embed (B := 5) (some q,preCounters e []) := by
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i <;> simp [CounterFlow.input,embed,preCounters,stackCode]

theorem compiled_halt (c : ToPartrec.Code) (e : ℕ) :
    (∃ t, (((compiledRecognizer c).step)^[t] ((compiledRecognizer c).initial e)).control =
      (compiledRecognizer c).halt) ↔ (c.eval [2^e]).Dom := by
  let S := codeSupp c .halt
  let hs : Closed S := (tr_supports c .halt).2
  let entry := trNormal c .halt
  let he : entry ∈ S := (tr_supports c .halt).1
  change (∃ t, (((CounterFlow.program (by decide : 0 < 6)
    (table (by decide : 0 < 5) (machine S hs entry he)) (.run (.inl 0))).step)^[t]
      ((CounterFlow.program (by decide : 0 < 6)
        (table (by decide : 0 < 5) (machine S hs entry he)) (.run (.inl 0))).initial e)).control =
          (CounterFlow.program (by decide : 0 < 6)
            (table (by decide : 0 < 5) (machine S hs entry he)) (.run (.inl 0))).halt) ↔ _
  rw [CounterFlow.halt_iff,low_input,macro_halt_iff]
  have htr : Tr S (init c [2^e])
      (some (.inr (node S entry he,none)),preCounters 0 (trList [2^e])) := by
    refine ⟨(node S entry he).property,?_⟩
    simp [init,node,preCounters_zero,entry]
  calc
    (∃ t, ((mstep S hs entry he)^[t] (some (.inl 0),preCounters e [])).1 = none) ↔
        (eval (CounterTermination.next (mstep S hs entry he))
          (some (.inl 0),preCounters e [])).Dom := (CounterTermination.dom_iff _ _).symm
    _ ↔ (eval (CounterTermination.next (mstep S hs entry he))
        (some (.inr (node S entry he,none)),preCounters 0 (trList [2^e]))).Dom :=
      Iff.of_eq (congrArg Part.Dom (reaches_eval (input_preamble S hs entry he e)))
    _ ↔ (eval (TM2.step tr) (init c [2^e])).Dom :=
      tr_eval_dom (tm2_respects S hs entry he) htr
    _ ↔ (c.eval [2^e]).Dom := by
      simpa using congrArg Part.Dom (PartrecToTM2.tr_eval c [2^e])

theorem exists_correct : ∃ p : CounterProgram, RecognizesK p := by
  obtain ⟨c,hc⟩ := universal_code
  exact ⟨compiledRecognizer c,fun e => (compiled_halt c e).trans (hc e)⟩

end E2.RecognizerImplementation