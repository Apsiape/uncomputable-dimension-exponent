import E2.RecognizerTM2

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2 Function CounterStack Relation StateTransition
variable (S : Finset Λ') (hs : Closed S) (entry : Λ') (he : entry ∈ S)

theorem stmt_path (q : Stmt') (hq : some q ∈ TM2.stmts tr S)
    (s : Option Γ') (T : K' → List Γ') :
    ∃ d, Tr S (TM2.stepAux q s T) d ∧
      Reaches₁ (CounterTermination.next (mstep S hs entry he))
        (some (.inr (⟨q,hq⟩,s)),counters T) d := by
  classical
  induction q generalizing s T with
  | push k f q ih =>
    have hchild := TM2.stmts_trans (show q ∈ TM2.stmts₁ (.push k f q) by
      exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
    obtain ⟨d,hd,hpath⟩ := ih hchild s (update T k (f s::T k))
    refine ⟨d,hd,TransGen.head ?_ hpath⟩
    simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm,counters_push]
  | pop k f q ih =>
    have hchild := TM2.stmts_trans (show q ∈ TM2.stmts₁ (.pop k f q) by
      exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
    obtain ⟨d,hd,hpath⟩ := ih hchild (f s (T k).head?) (update T k (T k).tail)
    refine ⟨d,hd,TransGen.head ?_ hpath⟩
    simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm,
      counters_pop,counters_reg,stackCode_mod]
  | peek k f q ih =>
    have hchild := TM2.stmts_trans (show q ∈ TM2.stmts₁ (.peek k f q) by
      exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
    obtain ⟨d,hd,hpath⟩ := ih hchild (f s (T k).head?) T
    refine ⟨d,hd,TransGen.head ?_ hpath⟩
    simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm,
      counters_reg,stackCode_mod]
  | load f q ih =>
    have hchild := TM2.stmts_trans (show q ∈ TM2.stmts₁ (.load f q) by
      exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
    obtain ⟨d,hd,hpath⟩ := ih hchild (f s) T
    refine ⟨d,hd,TransGen.head ?_ hpath⟩
    simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm]
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f s
    · have hchild := TM2.stmts_trans (show q₂ ∈ TM2.stmts₁ (.branch f q₁ q₂) by
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self)) hq
      obtain ⟨d,hd,hpath⟩ := ih₂ hchild s T
      refine ⟨d,by simpa [TM2.stepAux,hf] using hd,TransGen.head ?_ hpath⟩
      simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm,hf]
    · have hchild := TM2.stmts_trans (show q₁ ∈ TM2.stmts₁ (.branch f q₁ q₂) by
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self)) hq
      obtain ⟨d,hd,hpath⟩ := ih₁ hchild s T
      refine ⟨d,by simpa [TM2.stepAux,hf] using hd,TransGen.head ?_ hpath⟩
      simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm,hf]
  | goto f =>
    let n := node S (f s) (node_support S hs _ hq s)
    refine ⟨(some (.inr (n,s)),counters T),?_,TransGen.single ?_⟩
    · exact ⟨n.property,rfl⟩
    · simp [n,CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm]
  | halt =>
    refine ⟨(none,counters T),rfl,TransGen.single ?_⟩
    simp [CounterTermination.next,mstep,machine,compileStmt,macroStep,subnode,counters_update,stackCode,Nat.add_comm]

theorem tm2_respects :
    Respects (TM2.step tr) (CounterTermination.next (mstep S hs entry he)) (Tr S) := by
  rintro ⟨l,s,T⟩ d hd
  cases l with
  | none =>
    change d = (none,counters T) at hd
    subst d
    rfl
  | some l =>
    obtain ⟨hq,rfl⟩ := hd
    exact stmt_path S hs entry he (tr l) hq s T

theorem tm2_halt_iff (c : Cfg') (d : CounterFlow.Cfg 5 (Labels S)) (h : Tr S c d) :
    (∃ t, ((mstep S hs entry he)^[t] d).1 = none) ↔
      (StateTransition.eval (TM2.step tr) c).Dom := by
  rw [← CounterTermination.dom_iff]
  exact tr_eval_dom (tm2_respects S hs entry he) h

end E2.RecognizerImplementation