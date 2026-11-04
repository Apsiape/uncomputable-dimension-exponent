import E2.ProgramCore
import Mathlib.Data.Fintype.EquivFin

namespace E2.CounterFlow

inductive Op (r : ℕ) (Q : Type*)
  | inc : Fin r → Q → Op r Q
  | dec : Fin r → Q → Q → Op r Q
  | jump : Q → Op r Q
  | halt : Op r Q
  | stay : Op r Q

abbrev Cfg (r : ℕ) (Q : Type*) := Option Q × (Fin r → ℕ)

def step {r : ℕ} {Q : Type*} (I : Q → Op r Q) : Cfg r Q → Cfg r Q
  | (none,v) => (none,v)
  | (some q,v) => match I q with
    | .inc i k => (some k, Function.update v i (v i+1))
    | .dec i k₀ k₁ => if v i = 0 then (some k₀,v)
      else (some k₁,Function.update v i (v i-1))
    | .jump k => (some k,v)
    | .halt => (none,v)
    | .stay => (some q,v)

abbrev Labels (Q : Type*) := Option (Option (Option Q))

noncomputable def encode {Q : Type*} [Fintype Q] (q : Option Q) :
    Fin (Fintype.card (Labels Q)) :=
  Fintype.equivFin (Labels Q) (some (some q))

noncomputable def program {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) : CounterProgram where
  counters := r
  controls := Fintype.card (Labels Q)
  counters_pos := hr
  start := Fintype.equivFin (Labels Q) none
  idle := Fintype.equivFin (Labels Q) (some none)
  halt := encode none
  distinct := by
    simp [encode]
  instruction := fun k => match (Fintype.equivFin (Labels Q)).symm k with
    | none => .jump (encode (some entry))
    | some none => .stay
    | some (some none) => .stay
    | some (some (some q)) => match I q with
      | .inc i k => .inc i (encode (some k))
      | .dec i k₀ k₁ => .dec i (encode (some k₀)) (encode (some k₁))
      | .jump k => .jump (encode (some k))
      | .halt => .jump (encode none)
      | .stay => .stay
  idle_absorbing := by simp
  halt_absorbing := by simp [encode]

noncomputable def liftCfg {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) (c : Cfg r Q) :
    Configuration (program hr I entry) := ⟨encode c.1,c.2⟩

theorem step_lift {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) (c : Cfg r Q) :
    (program hr I entry).step (liftCfg hr I entry c) =
      liftCfg hr I entry (step I c) := by
  rcases c with ⟨q,v⟩
  cases q with
  | none => simp [CounterProgram.step,liftCfg,program,encode,step]
  | some q =>
    simp only [CounterProgram.step, liftCfg, program, encode, Equiv.symm_apply_apply]
    cases h : I q <;> simp only [h,step] <;> try rfl
    case dec i a b =>
      by_cases hv : v i = 0 <;>
        simp_all [CounterProgram.step,liftCfg,program,encode,step] <;> rfl

noncomputable def input {r : ℕ} (Q : Type*) (entry : Q) (e : ℕ) : Cfg r Q :=
  (some entry,fun i => if i.val = 0 then e else 0)

theorem initial_step {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) (e : ℕ) :
    (program hr I entry).step ((program hr I entry).initial e) =
      liftCfg hr I entry (input Q entry e) := by
  simp [CounterProgram.step,CounterProgram.initial,program,liftCfg,input]

theorem iterate_lift {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) (c : Cfg r Q) (n : ℕ) :
    ((program hr I entry).step)^[n] (liftCfg hr I entry c) =
      liftCfg hr I entry ((step I)^[n] c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,step_lift,Function.iterate_succ_apply']

theorem halt_iff {r : ℕ} {Q : Type*} [Fintype Q]
    (hr : 0 < r) (I : Q → Op r Q) (entry : Q) (e : ℕ) :
    (∃ t, (((program hr I entry).step)^[t]
      ((program hr I entry).initial e)).control = (program hr I entry).halt) ↔
    ∃ t, ((step I)^[t] (input Q entry e)).1 = none := by
  have h (t : ℕ) :
      (((program hr I entry).step)^[t+1] ((program hr I entry).initial e)).control =
        encode (((step I)^[t] (input Q entry e)).1) := by
    rw [Function.iterate_succ_apply,initial_step,iterate_lift]
    rfl
  constructor
  · rintro ⟨t,ht⟩
    cases t with
    | zero =>
      exact False.elim ((program hr I entry).distinct.2.1 ht)
    | succ t =>
      rw [h] at ht
      exact ⟨t,by simpa only [program,encode,Equiv.apply_eq_iff_eq,
        Option.some.injEq] using ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨t+1,by rw [h,ht]; rfl⟩

end E2.CounterFlow