import E2.Computability

namespace E2

inductive Instruction (r q : ℕ)
  | inc : Fin r → Fin q → Instruction r q
  | dec : Fin r → Fin q → Fin q → Instruction r q
  | jump : Fin q → Instruction r q
  | stay : Instruction r q
  deriving DecidableEq, Repr

structure CounterProgram where
  counters : ℕ
  controls : ℕ
  counters_pos : 0 < counters
  start : Fin controls
  idle : Fin controls
  halt : Fin controls
  distinct : start ≠ idle ∧ start ≠ halt ∧ idle ≠ halt
  instruction : Fin controls → Instruction counters controls
  idle_absorbing : instruction idle = .stay
  halt_absorbing : instruction halt = .stay

structure Configuration (p : CounterProgram) where
  control : Fin p.controls
  counter : Fin p.counters → ℕ

def CounterProgram.step (p : CounterProgram) (c : Configuration p) : Configuration p :=
  match p.instruction c.control with
  | .inc i q => ⟨q, Function.update c.counter i (c.counter i + 1)⟩
  | .dec i q₀ q₁ => if c.counter i = 0 then ⟨q₀, c.counter⟩
    else ⟨q₁, Function.update c.counter i (c.counter i - 1)⟩
  | .jump q => ⟨q, c.counter⟩
  | .stay => c

def CounterProgram.initial (p : CounterProgram) (e : ℕ) : Configuration p :=
  ⟨p.start, fun i => if i.val = 0 then e else 0⟩

def RecognizesK (p : CounterProgram) : Prop :=
  ∀ e, (∃ t, ((p.step)^[t] (p.initial e)).control = p.halt) ↔ e ∈ haltingSet

end E2
