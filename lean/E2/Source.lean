import E2.Presentation
import E2.Program
import Lean.Elab.Tactic.Omega

/-! Section 5 as an actual finite list of rational *-polynomials.
Indices 0..11 are (A,P,T,X) for address/fuel/time; 12..22 are
(V,U,H,L,R,Z,F,B,C,Q,Y); then (r,z,s) for each counter, then controls.
-/
namespace E2
open Poly

def sourceSize (p : CounterProgram) : ℕ := 23 + 3 * p.counters + p.controls
abbrev SourceVar (p : CounterProgram) := Fin (sourceSize p)
abbrev SourcePoly (p : CounterProgram) := Poly (SourceVar p)

def sv (p : CounterProgram) (n : ℕ) : SourcePoly p :=
  .var ⟨n % sourceSize p, Nat.mod_lt _ (by unfold sourceSize; omega)⟩
def sr (p : CounterProgram) (i : Fin p.counters) := sv p (23 + 3 * i.val)
def sz (p : CounterProgram) (i : Fin p.counters) := sv p (24 + 3 * i.val)
def ss (p : CounterProgram) (i : Fin p.counters) := sv p (25 + 3 * i.val)
def sq (p : CounterProgram) (i : Fin p.controls) := sv p (23 + 3 * p.counters + i.val)
def pc {ι : Type*} (a b : Poly ι) := a * b - b * a
def conjP {ι : Type*} (t a : Poly ι) := t * a * t.adj
def psum {ι : Type*} (xs : List (Poly ι)) := xs.foldr (· + ·) 0
def commList {ι : Type*} (xs ys : List (Poly ι)) : List (Poly ι) :=
  xs.flatMap (fun x => ys.map (pc x))

def clockRelations {ι : Type*} (a p t x : Poly ι) : List (Poly ι) :=
  [pc a p, conjP t a - (4 * a - 3 * p), x * p * x - (1 - p), pc x (conjP t a)]

def guardRelation {ι : Type*} (a p t x v : Poly ι) : Poly ι :=
  (v - x * ((1 - p) + conjP t v * p)) * (1 - a)

structure ProgramBranch (p : CounterProgram) where
  selector : SourcePoly p
  target : Fin p.controls
  scale : Fin p.counters → ℚ

def programBranches (p : CounterProgram) : List (ProgramBranch p) :=
  (List.finRange p.controls).flatMap fun q =>
    match p.instruction q with
    | .inc i q' => [⟨sq p q, q', fun j => if j = i then 1/2 else 1⟩]
    | .dec i q₀ q₁ =>
      [⟨sq p q * sz p i, q₀, fun _ => 1⟩,
       ⟨sq p q * (1 - sz p i), q₁, fun j => if j = i then 2 else 1⟩]
    | .jump q' => [⟨sq p q, q', fun _ => 1⟩]
    | .stay => [⟨sq p q, q, fun _ => 1⟩]

def nextCounter (p : CounterProgram) (i : Fin p.counters) : SourcePoly p :=
  psum ((programBranches p).map fun b => b.selector * .const (b.scale i) * sr p i)
def nextControl (p : CounterProgram) (q : Fin p.controls) : SourcePoly p :=
  psum ((programBranches p).map fun b => if b.target = q then b.selector else 0)
def initialCounter (p : CounterProgram) (i : Fin p.counters) : SourcePoly p :=
  if i.val = 0 then sv p 16 else 1
def initialControl (p : CounterProgram) (q : Fin p.controls) : SourcePoly p :=
  if q = p.start then sv p 15 else if q = p.idle then 1 - sv p 15 else 0

def sourceDomain (p : CounterProgram) (i : SourceVar p) : Domain :=
  if i.val < 12 then
    match i.val % 4 with
    | 0 => .positiveContraction | 1 => .projection | 2 => .unitary | _ => .reflection
  else if i.val = 12 ∨ i.val = 13 then .unitary
  else if i.val = 22 then .reflection
  else if i.val = 15 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 21 then .projection
  else if i.val < 23 then .positiveContraction
  else if i.val < 23 + 3 * p.counters then
    if (i.val - 23) % 3 = 1 then .projection else .positiveContraction
  else .projection

def sourceRelations (p : CounterProgram) : List (SourcePoly p) := Id.run do
  let v := sv p
  let addr := [v 0, v 1, v 2, v 3, v 12, v 14]
  let fuel := [v 4, v 5, v 6, v 7]
  let time := [v 8, v 9, v 10, v 11, v 13]
  let work := (List.finRange p.counters).flatMap (fun i => [sr p i, sz p i, ss p i]) ++
    (List.finRange p.controls).map (sq p)
  let e00 := (1 - v 1) * (1 - conjP (v 2) (v 1))
  let e1 := v 1 * (1 - conjP (v 2) (v 1))
  let zplus := conjP (v 13).adj (v 17)
  let update := fun w ini nxt =>
    [v 17 * w - v 17 * ini,
     conjP (v 13).adj w - (zplus * ini + (1 - zplus) * nxt)]
  return clockRelations (v 0) (v 1) (v 2) (v 3) ++
    clockRelations (v 4) (v 5) (v 6) (v 7) ++
    clockRelations (v 8) (v 9) (v 10) (v 11) ++
    commList addr fuel ++ commList addr time ++ commList fuel time ++
    [guardRelation (v 0) (v 1) (v 2) (v 3) (v 12),
     guardRelation (v 8) (v 9) (v 10) (v 11) (v 13),
     v 14 - ((1 - v 1) + .const (1/4) * v 1 * conjP (v 2) (v 14)),
     pc (v 1) (conjP (v 2) (v 14)), pc (v 14) (v 0),
     conjP (v 12).adj (v 0) - (v 0 - 1 + .const (7/4) * v 14),
     v 15 - (e1 + e00 * conjP (v 2 ^ 2) (v 15)),
     v 16 - ((1 - e00) + .const (1/2) * e00 * conjP (v 2 ^ 2) (v 16)),
     v 17 - ((1 - v 5) + v 5 * (1 - v 9) * conjP (v 6 * v 10) (v 17))] ++
    (List.finRange p.counters).map (fun i =>
      sr p i - (sz p i + .const (1/2) * (1 - sz p i) * ss p i)) ++
    (List.finRange p.controls).flatMap (fun q =>
      ((List.finRange p.controls).filter (· != q)).map (fun q' => sq p q * sq p q')) ++
    [psum ((List.finRange p.controls).map (sq p)) - 1] ++
    (List.finRange p.counters).flatMap (fun i => update (sr p i) (initialCounter p i) (nextCounter p i)) ++
    (List.finRange p.controls).flatMap (fun q => update (sq p q) (initialControl p q) (nextControl p q)) ++
    [(1 - v 18) * sq p p.halt] ++
    commList [v 15, v 16, v 18] [v 15, v 16, v 18] ++
    commList [v 15, v 16, v 18] ([v 0] ++ fuel ++ time) ++
    commList (v 17 :: work) (v 17 :: work) ++
    commList (v 17 :: work) [v 0, v 4, v 8, v 15, v 16, v 18] ++
    [(1 - v 18) * v 21,
     pc (v 19) (v 21), pc (v 19) (v 18), pc (v 20) (v 21), pc (v 20) (v 18),
     pc (v 19) (v 20),
     conjP (v 12) (v 19) - (4 * v 19 - 3 * v 21),
     conjP (v 12) (v 20) - (4 * v 20 - 3 * v 18),
     v 22 * v 18 * v 22 - v 18,
     v 22 * v 21 * v 22 - (v 18 - v 21),
     pc (v 22) (conjP (v 12) (v 19)), pc (v 22) (v 20)] ++
    commList [v 19, v 20, v 21, v 22] ([v 0] ++ fuel ++ time)

def sourcePresentation (p : CounterProgram) : Presentation (SourceVar p) :=
  ⟨sourceDomain p, sourceRelations p⟩

noncomputable def PK := sourcePresentation recognizer

end E2
