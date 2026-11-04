import E2.RecognizerTM2

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2 Function CounterStack Relation StateTransition

def powBits : ℕ → PosNum
  | 0 => .one
  | n+1 => .bit0 (powBits n)

theorem powBits_val (n : ℕ) : (powBits n : ℕ) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [powBits,PosNum.cast_bit0,ih,pow_succ]; omega

theorem trList_pow (n : ℕ) :
    trList [2^n] = (List.cons Γ'.bit0)^[n] [Γ'.bit1,Γ'.cons] := by
  have h (n : ℕ) : trNat (2^n) = trPosNum (powBits n) := by
    have he : ((2^n : ℕ) : Num) = Num.pos (powBits n) := by
      rw [← powBits_val n]
      exact Num.of_to_nat (Num.pos (powBits n))
    simp only [trNat,he,trNum]
  simp only [trList,h,List.append_nil]
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [powBits,trPosNum,List.cons_append,iterate_succ_apply'] using
      (congrArg (List.cons Γ'.bit0) ih)

def preCounters (e : ℕ) (l : List Γ') : Fin 5 → ℕ := ![e,stackCode l,0,0,0]

@[simp] theorem preCounters_read (e : ℕ) (l : List Γ') : preCounters e l 0 = e := rfl

@[simp] theorem preCounters_zero (l : List Γ') : preCounters 0 l =
    counters (K'.elim l [] [] []) := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem preCounters_input (e n : ℕ) (l : List Γ') :
    update (preCounters e l) 0 n = preCounters n l := by
  funext i
  fin_cases i <;> simp [preCounters]

theorem preCounters_push (e : ℕ) (l : List Γ') (a : Γ') :
    update (preCounters e l) (reg .main) (5*preCounters e l (reg .main)+(digit a).val) =
      preCounters e (a::l) := by
  funext i
  fin_cases i <;> simp [preCounters,reg,stackCode,Nat.add_comm]

variable (S : Finset Λ') (hs : Closed S) (entry : Λ') (he : entry ∈ S)

theorem input_loop (e : ℕ) (l : List Γ') :
    Reaches (CounterTermination.next (mstep S hs entry he))
      (some (.inl 2),preCounters e l)
      (some (.inr (node S entry he,none)),
        preCounters 0 ((List.cons Γ'.bit0)^[e] l)) := by
  induction e generalizing l with
  | zero =>
    exact ReflTransGen.single (by
      simp [CounterTermination.next,mstep,machine,macroStep,preCounters])
  | succ e ih =>
    have h₁ : (some (.inl 3),preCounters e l) ∈
        CounterTermination.next (mstep S hs entry he) (some (.inl 2),preCounters (e+1) l) := by
      simp [CounterTermination.next,mstep,machine,macroStep,preCounters_input,preCounters_read]
    have h₂ : (some (.inl 2),preCounters e (.bit0::l)) ∈
        CounterTermination.next (mstep S hs entry he) (some (.inl 3),preCounters e l) := by
      simp [CounterTermination.next,mstep,machine,macroStep,preCounters_push]
    simpa only [iterate_succ_apply,StateTransition.Reaches] using
      (ReflTransGen.single (r := fun a b => b ∈ CounterTermination.next (mstep S hs entry he) a) h₁).trans ((ReflTransGen.single (r := fun a b => b ∈ CounterTermination.next (mstep S hs entry he) a) h₂).trans (ih (.bit0::l)))

theorem input_preamble (e : ℕ) :
    Reaches (CounterTermination.next (mstep S hs entry he))
      (some (.inl 0),preCounters e [])
      (some (.inr (node S entry he,none)),preCounters 0 (trList [2^e])) := by
  have h₁ : (some (.inl 1),preCounters e [.cons]) ∈
      CounterTermination.next (mstep S hs entry he) (some (.inl 0),preCounters e []) := by
    simp [CounterTermination.next,mstep,machine,macroStep,preCounters_push]
  have h₂ : (some (.inl 2),preCounters e [.bit1,.cons]) ∈
      CounterTermination.next (mstep S hs entry he) (some (.inl 1),preCounters e [.cons]) := by
    simp [CounterTermination.next,mstep,machine,macroStep,preCounters_push]
  rw [trList_pow]
  exact (ReflTransGen.single (r := fun a b => b ∈ CounterTermination.next (mstep S hs entry he) a) h₁).trans ((ReflTransGen.single (r := fun a b => b ∈ CounterTermination.next (mstep S hs entry he) a) h₂).trans
    (input_loop S hs entry he e [.bit1,.cons]))

end E2.RecognizerImplementation