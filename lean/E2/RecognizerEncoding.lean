import E2.CounterMacro
import Mathlib.Computability.TuringMachine.ToPartrec

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2 Function

def digit : Γ' → Fin 5
  | .consₗ => 1
  | .cons => 2
  | .bit0 => 3
  | .bit1 => 4

def undigit (d : Fin 5) : Option Γ' :=
  match d.val with
  | 1 => some .consₗ
  | 2 => some .cons
  | 3 => some .bit0
  | 4 => some .bit1
  | _ => none

def stackCode : List Γ' → ℕ
  | [] => 0
  | a::l => (digit a).val+5*stackCode l

@[simp] theorem undigit_digit (a : Γ') : undigit (digit a) = some a := by
  cases a <;> rfl

@[simp] theorem stackCode_mod (l : List Γ') :
    undigit ⟨stackCode l%5,by omega⟩ = l.head? := by
  cases l with
  | nil => rfl
  | cons a l =>
    have h : ((digit a).val+5*stackCode l)%5 = (digit a).val := by
      have := (digit a).isLt
      omega
    simp only [stackCode,h,List.head?_cons]
    change undigit (digit a) = some a
    exact undigit_digit a

@[simp] theorem stackCode_div (l : List Γ') :
    stackCode l/5 = stackCode l.tail := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [stackCode,List.tail_cons]
    have := (digit a).isLt
    omega

def reg : K' → Fin 5
  | .main => 1
  | .rev => 2
  | .aux => 3
  | .stack => 4

def counters (S : K' → List Γ') : Fin 5 → ℕ :=
  ![0,stackCode (S .main),stackCode (S .rev),stackCode (S .aux),stackCode (S .stack)]

@[simp] theorem counters_reg (S : K' → List Γ') (k : K') :
    counters S (reg k) = stackCode (S k) := by cases k <;> simp [counters,reg]

theorem counters_update (S : K' → List Γ') (k : K') (l : List Γ') :
    counters (update S k l) = update (counters S) (reg k) (stackCode l) := by
  funext i
  fin_cases i <;> cases k <;> simp [counters,reg,update_apply]

theorem counters_push (S : K' → List Γ') (k : K') (a : Γ') :
    update (counters S) (reg k) (5*counters S (reg k)+(digit a).val) =
      counters (update S k (a::S k)) := by
  rw [counters_update,counters_reg,stackCode]
  congr 1
  omega

theorem counters_pop (S : K' → List Γ') (k : K') :
    update (counters S) (reg k) (counters S (reg k)/5) =
      counters (update S k (S k).tail) := by
  rw [counters_update,counters_reg,stackCode_div]

end E2.RecognizerImplementation