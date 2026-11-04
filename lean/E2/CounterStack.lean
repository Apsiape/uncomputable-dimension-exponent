import E2.CounterFlow
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Computability.StateTransition

namespace E2.CounterStack
open CounterFlow
open Function
open Relation

inductive Macro (r B : ℕ) (Q : Type*)
  | inc : Fin r → Q → Macro r B Q
  | dec : Fin r → Q → Q → Macro r B Q
  | jump : Q → Macro r B Q
  | push : Fin r → Fin B → Q → Macro r B Q
  | pop : Fin r → (Fin B → Q) → Macro r B Q
  | peek : Fin r → (Fin B → Q) → Macro r B Q
  | halt : Macro r B Q

inductive Ctrl (r B : ℕ) (Q : Type*)
  | run : Q → Ctrl r B Q
  | mul : Fin r → Fin B → Q → Ctrl r B Q
  | mulAdd : Fin r → Fin B → Q → Fin (B+1) → Ctrl r B Q
  | flush : Fin r → Fin B → Q → Ctrl r B Q
  | flushInc : Fin r → Fin B → Q → Ctrl r B Q
  | add : Fin r → Fin B → Q → Ctrl r B Q
  | div : Fin r → (Fin B → Q) → Bool → Fin B → Ctrl r B Q
  | carry : Fin r → (Fin B → Q) → Bool → Ctrl r B Q
  | out : Fin r → (Fin B → Q) → Bool → Fin B → Ctrl r B Q
  | outInc : Fin r → (Fin B → Q) → Bool → Fin B → Ctrl r B Q

set_option synthInstance.maxSize 2048 in
noncomputable instance (r B : ℕ) (Q : Type*) [Fintype Q] : Fintype (Ctrl r B Q) := by
  classical
  exact derive_fintype% _

variable {r B : ℕ} {Q : Type*}

def table (hB : 0 < B) (M : Q → Macro r B Q) : Ctrl r B Q → Op (r+1) (Ctrl r B Q)
  | .run q => match M q with
    | .inc i k => .inc i.castSucc (.run k)
    | .dec i a b => .dec i.castSucc (.run a) (.run b)
    | .jump k => .jump (.run k)
    | .push i d k => .jump (.mul i d k)
    | .pop i f => .jump (.div i f false ⟨0,hB⟩)
    | .peek i f => .jump (.div i f true ⟨0,hB⟩)
    | .halt => .halt
  | .mul i d k => .dec i.castSucc (.flush i d k) (.mulAdd i d k ⟨B,by omega⟩)
  | .mulAdd i d k j => if h : j.val = 0 then .jump (.mul i d k)
    else .inc (Fin.last r) (.mulAdd i d k ⟨j.val-1,by omega⟩)
  | .flush i d k => .dec (Fin.last r) (.add i d k) (.flushInc i d k)
  | .flushInc i d k => .inc i.castSucc (.flush i d k)
  | .add i j k => if h : j.val = 0 then .jump (.run k)
    else .inc i.castSucc (.add i ⟨j.val-1,by omega⟩ k)
  | .div i f peek a => .dec i.castSucc (.out i f peek a)
    (if h : a.val+1 < B then .div i f peek ⟨a.val+1,h⟩ else .carry i f peek)
  | .carry i f peek => .inc (Fin.last r) (.div i f peek ⟨0,hB⟩)
  | .out i f peek a => .dec (Fin.last r)
    (if peek then .mul i a (f a) else .run (f a)) (.outInc i f peek a)
  | .outInc i f peek a => .inc i.castSucc (.out i f peek a)

abbrev Reach (hB : 0 < B) (M : Q → Macro r B Q) :=
  ReflTransGen (fun a b : Cfg (r+1) (Ctrl r B Q) => step (table hB M) a = b)

variable (hB : 0 < B) (M : Q → Macro r B Q)

theorem one {a b : Cfg (r+1) (Ctrl r B Q)}
    (h : step (table hB M) a = b) : Reach hB M a b := .single h

def put (v : Fin r → ℕ) (i : Fin r) (n m : ℕ) : Fin (r+1) → ℕ :=
  Fin.snoc (update v i n) m

@[simp] theorem put_i (v : Fin r → ℕ) (i : Fin r) (n m : ℕ) :
    put v i n m i.castSucc = n := by simp [put]

@[simp] theorem put_scratch (v : Fin r → ℕ) (i : Fin r) (n m : ℕ) :
    put v i n m (Fin.last r) = m := by simp [put]

@[simp] theorem put_update_i (v : Fin r → ℕ) (i : Fin r) (n m k : ℕ) :
    update (put v i n m) i.castSucc k = put v i k m := by
  simp [put,← Fin.snoc_update,update_idem]

@[simp] theorem put_update_scratch (v : Fin r → ℕ) (i : Fin r) (n m k : ℕ) :
    update (put v i n m) (Fin.last r) k = put v i n k := by
  exact @Fin.update_snoc_last r (fun _ => ℕ) m (update v i n) k

theorem mulAdd_correct (i : Fin r) (d : Fin B) (k : Q)
    (v : Fin r → ℕ) (n m j : ℕ) (hj : j ≤ B) :
    Reach hB M (some (.mulAdd i d k ⟨j,by omega⟩),put v i n m)
      (some (.mul i d k),put v i n (m+j)) := by
  induction j generalizing m with
  | zero => exact one hB M (by simp [step,table])
  | succ j ih =>
    have h := one hB M (a := (some (.mulAdd i d k ⟨j+1,by omega⟩),put v i n m))
      (b := (some (.mulAdd i d k ⟨j,by omega⟩),put v i n (m+1)))
      (by simp [step,table])
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      h.trans (ih (m+1) (by omega))

theorem mul_correct (i : Fin r) (d : Fin B) (k : Q)
    (v : Fin r → ℕ) (n m : ℕ) :
    Reach hB M (some (.mul i d k),put v i n m)
      (some (.flush i d k),put v i 0 (m+B*n)) := by
  induction n generalizing m with
  | zero => exact one hB M (by simp [step,table])
  | succ n ih =>
    have h := one hB M (a := (some (.mul i d k),put v i (n+1) m))
      (b := (some (.mulAdd i d k ⟨B,by omega⟩),put v i n m))
      (by simp [step,table])
    have h := h.trans (mulAdd_correct hB M i d k v n m B (le_refl B))
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.trans (ih (m+B))

theorem add_correct (i : Fin r) (k : Q) (v : Fin r → ℕ)
    (n j : ℕ) (hj : j < B) :
    Reach hB M (some (.add i ⟨j,hj⟩ k),put v i n 0)
      (some (.run k),put v i (n+j) 0) := by
  induction j generalizing n with
  | zero => exact one hB M (by simp [step,table])
  | succ j ih =>
    have h := one hB M (a := (some (.add i ⟨j+1,hj⟩ k),put v i n 0))
      (b := (some (.add i ⟨j,by omega⟩ k),put v i (n+1) 0))
      (by simp [step,table])
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      h.trans (ih (n+1) (by omega))

theorem flush_correct (i : Fin r) (d : Fin B) (k : Q)
    (v : Fin r → ℕ) (n m : ℕ) :
    Reach hB M (some (.flush i d k),put v i n m)
      (some (.add i d k),put v i (n+m) 0) := by
  induction m generalizing n with
  | zero => exact one hB M (by simp [step,table])
  | succ m ih =>
    have h := one hB M (a := (some (.flush i d k),put v i n (m+1)))
      (b := (some (.flushInc i d k),put v i n m))
      (by simp [step,table])
    have hh := one hB M (a := (some (.flushInc i d k),put v i n m))
      (b := (some (.flush i d k),put v i (n+1) m))
      (by simp [step,table])
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.trans (hh.trans (ih (n+1)))

theorem push_correct (i : Fin r) (d : Fin B) (k : Q) (v : Fin r → ℕ) :
    Reach hB M (some (.mul i d k),Fin.snoc v 0)
      (some (.run k),Fin.snoc (update v i (B*v i+d.val)) 0) := by
  have h := mul_correct hB M i d k v (v i) 0
  have hh := flush_correct hB M i d k v 0 (B*v i)
  have hhh := add_correct hB M i k v (B*v i) d.val d.isLt
  simp only [Nat.zero_add] at h hh
  simpa [put] using h.trans (hh.trans hhh)

end E2.CounterStack