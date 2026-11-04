import E2.CounterTermination

namespace E2.CounterStack
open CounterFlow Function Relation StateTransition
variable {r B : ℕ} {Q : Type*}

def macroStep (hB : 0 < B) (M : Q → Macro r B Q) : Cfg r Q → Cfg r Q
  | (none,v) => (none,v)
  | (some q,v) => match M q with
    | .inc i k => (some k,update v i (v i+1))
    | .dec i a b => if v i = 0 then (some a,v) else (some b,update v i (v i-1))
    | .jump k => (some k,v)
    | .push i d k => (some k,update v i (B*v i+d.val))
    | .pop i f => (some (f ⟨v i%B,Nat.mod_lt _ hB⟩),update v i (v i/B))
    | .peek i f => (some (f ⟨v i%B,Nat.mod_lt _ hB⟩),v)
    | .halt => (none,v)

def embed (c : Cfg r Q) : Cfg (r+1) (Ctrl r B Q) :=
  (c.1.map Ctrl.run,Fin.snoc c.2 0)

variable (hB : 0 < B) (M : Q → Macro r B Q)

theorem macro_correct (q : Q) (v : Fin r → ℕ) :
    Reaches₁ (CounterTermination.next (step (table hB M)))
      (embed (B := B) (some q,v)) (embed (macroStep hB M (some q,v))) := by
  cases hm : M q with
  | inc i k =>
    apply TransGen.single
    simp [CounterTermination.next,step,table,embed,macroStep,hm,Fin.snoc_update]
  | dec i a b =>
    by_cases hv : v i = 0
    all_goals
      apply TransGen.single
      simp [CounterTermination.next,step,table,embed,macroStep,hm,hv,Fin.snoc_update]
  | jump k =>
    exact TransGen.single (by simp [CounterTermination.next,step,table,embed,macroStep,hm])
  | halt =>
    exact TransGen.single (by simp [CounterTermination.next,step,table,embed,macroStep,hm])
  | push i d k =>
    apply TransGen.head'_iff.mpr
    refine ⟨(some (.mul i d k),Fin.snoc v 0),?_,?_⟩
    · simp [CounterTermination.next,step,table,embed,hm]
    · simpa [embed,macroStep,hm,StateTransition.Reaches,Option.mem_def] using CounterTermination.reach_of_total
        (step (table hB M)) (fun _ => rfl) (push_correct hB M i d k v) (by simp)
  | pop i f =>
    apply TransGen.head'_iff.mpr
    refine ⟨(some (.div i f false ⟨0,hB⟩),Fin.snoc v 0),?_,?_⟩
    · simp [CounterTermination.next,step,table,embed,hm]
    · simpa [embed,macroStep,hm,StateTransition.Reaches,Option.mem_def] using CounterTermination.reach_of_total
        (step (table hB M)) (fun _ => rfl) (pop_correct hB M i f v) (by simp)
  | peek i f =>
    apply TransGen.head'_iff.mpr
    refine ⟨(some (.div i f true ⟨0,hB⟩),Fin.snoc v 0),?_,?_⟩
    · simp [CounterTermination.next,step,table,embed,hm]
    · simpa [embed,macroStep,hm,StateTransition.Reaches,Option.mem_def] using CounterTermination.reach_of_total
        (step (table hB M)) (fun _ => rfl) (peek_correct hB M i f v) (by simp)

theorem macro_respects :
    Respects (CounterTermination.next (macroStep hB M))
      (CounterTermination.next (step (table hB M))) (fun a b => embed a = b) := by
  apply fun_respects.mpr
  rintro ⟨q,v⟩
  cases q with
  | none => rfl
  | some q => exact macro_correct hB M q v

theorem macro_halt_iff (c : Cfg r Q) :
    (∃ t, ((step (table hB M))^[t] (embed c)).1 = none) ↔
      ∃ t, ((macroStep hB M)^[t] c).1 = none := by
  rw [← CounterTermination.dom_iff,← CounterTermination.dom_iff]
  exact tr_eval_dom (macro_respects hB M) rfl

end E2.CounterStack