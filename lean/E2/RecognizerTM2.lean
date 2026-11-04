import E2.RecognizerEncoding

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2 Function CounterStack Relation StateTransition

abbrev Node (S : Finset Λ') := {q : Stmt' // some q ∈ TM2.stmts tr S}

noncomputable instance (S : Finset Λ') : Fintype (Node S) := by
  classical
  exact Fintype.ofInjective
    (fun q : Node S => (⟨some q.val,q.property⟩ : {a // a ∈ TM2.stmts tr S}))
    (fun a b h => Subtype.ext (Option.some.inj (congrArg Subtype.val h)))

abbrev Labels (S : Finset Λ') := Fin 4 ⊕ (Node S × Option Γ')

abbrev Closed (S : Finset Λ') := ∀ q ∈ S, TM2.SupportsStmt S (tr q)

theorem node_support (S : Finset Λ') (hs : Closed S) (q : Stmt')
    (hq : some q ∈ TM2.stmts tr S) : TM2.SupportsStmt S q := by
  classical
  have h := Finset.some_mem_insertNone.mp hq
  obtain ⟨l,hl,hql⟩ := Finset.mem_biUnion.mp h
  exact TM2.stmts₁_supportsStmt_mono hql (hs l hl)
noncomputable def node (S : Finset Λ') (q : Λ') (hq : q ∈ S) : Node S :=
  ⟨tr q,by
    classical
    apply Finset.some_mem_insertNone.mpr
    exact Finset.mem_biUnion.mpr ⟨q,hq,TM2.stmts₁_self⟩⟩

noncomputable def subnode {S : Finset Λ'} {q : Stmt'}
    (hq : some q ∈ TM2.stmts tr S) (q' : Stmt') (h : q' ∈ TM2.stmts₁ q) : Node S :=
  ⟨q',TM2.stmts_trans h hq⟩

noncomputable def compileStmt (S : Finset Λ') (hs : Closed S)
    (q : Stmt') (hq : some q ∈ TM2.stmts tr S) (s : Option Γ') : Macro 5 5 (Labels S) :=
  match q with
  | .push k f q' => .push (reg k) (digit (f s))
      (.inr (subnode hq q' (by
        classical
        exact Finset.mem_insert_of_mem TM2.stmts₁_self),s))
  | .pop k f q' => .pop (reg k) (fun d =>
      .inr (subnode hq q' (by
        classical
        exact Finset.mem_insert_of_mem TM2.stmts₁_self),f s (undigit d)))
  | .peek k f q' => .peek (reg k) (fun d =>
      .inr (subnode hq q' (by
        classical
        exact Finset.mem_insert_of_mem TM2.stmts₁_self),f s (undigit d)))
  | .load f q' => .jump (.inr (subnode hq q' (by
        classical
        exact Finset.mem_insert_of_mem TM2.stmts₁_self),f s))
  | .branch f q₁ q₂ => if f s then
      .jump (.inr (subnode hq q₁ (by
        classical
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self)),s)) else
      .jump (.inr (subnode hq q₂ (by
        classical
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self)),s))
  | .goto f => .jump (.inr (node S (f s) (node_support S hs _ hq s),s))
  | .halt => .halt

noncomputable def machine (S : Finset Λ') (hs : Closed S)
    (entry : Λ') (he : entry ∈ S) : Labels S → Macro 5 5 (Labels S)
  | .inr (q,s) => compileStmt S hs q.val q.property s
  | .inl i => match i.val with
    | 0 => .push (reg .main) (digit .cons) (.inl 1)
    | 1 => .push (reg .main) (digit .bit1) (.inl 2)
    | 2 => .dec 0 (.inr (node S entry he,none)) (.inl 3)
    | _ => .push (reg .main) (digit .bit0) (.inl 2)

variable (S : Finset Λ') (hs : Closed S) (entry : Λ') (he : entry ∈ S)

noncomputable abbrev mstep := macroStep (by decide : 0 < 5) (machine S hs entry he)

/-- Only supported labels enter the finite instruction table. -/
def Tr (c : Cfg') (d : CounterFlow.Cfg 5 (Labels S)) : Prop :=
  match c.l with
  | none => d = (none,counters c.stk)
  | some l => ∃ h : some (tr l) ∈ TM2.stmts tr S,
      d = (some (.inr (⟨tr l,h⟩,c.var)),counters c.stk)

end E2.RecognizerImplementation