import E2.FeasibilitySentence

namespace E2.FeasibilitySentence
noncomputable section
open RealArithmetic

abbrev RawEntry (G : BCSGame) := Bool ×
  (((ℕ × ℕ) × (ℕ × ℕ)) ⊕
   ((Fin G.contexts × (Fin G.numVars → Bool) × ℕ × ℕ) ⊕
    (Fin G.numVars × Bool × ℕ × ℕ)))

def rR (G : BCSGame) (b : Bool) (i j k l : ℕ) : CPoly :=
  cvar (Encodable.encode ((b,Sum.inl ((i,j),(k,l))) : RawEntry G))
def rA (G : BCSGame) (b : Bool) (c : Fin G.contexts) (a : Fin G.numVars → Bool) (i j : ℕ) : CPoly :=
  cvar (Encodable.encode ((b,Sum.inr (Sum.inl (c,a,i,j))) : RawEntry G))
def rB (G : BCSGame) (b : Bool) (w : Fin G.numVars) (a : Bool) (i j : ℕ) : CPoly :=
  cvar (Encodable.encode ((b,Sum.inr (Sum.inr (w,a,i,j))) : RawEntry G))
def rAll (d : ℕ) (f : ℕ → Sentence) : Sentence := (List.range d).flatMap f
def rTotal (d : ℕ) (f : ℕ → CPoly) : CPoly := csum ((List.range d).map f)
def rAll₂ (d : ℕ) (f : ℕ → ℕ → Sentence) : Sentence := rAll d fun i => rAll d (f i)
def rTotal₂ (d : ℕ) (f : ℕ → ℕ → CPoly) : CPoly := rTotal d fun i => rTotal d (f i)
def rEq (d : ℕ) (X Y : ℕ → ℕ → CPoly) : Sentence :=
  rAll₂ d fun i j => ceq (X i j) (Y i j)
def rGram (d : ℕ) (Y : ℕ → ℕ → CPoly) (i j : ℕ) : CPoly :=
  rTotal d fun k => cmul (cstar (Y k i)) (Y k j)
def rRGram (G : BCSGame) (d : ℕ) (b : Bool) (i j k l : ℕ) : CPoly :=
  rTotal₂ d fun p q => cmul (cstar (rR G b p q i j)) (rR G b p q k l)
def rIdentity (i j : ℕ) : CPoly := if i=j then cone else czero

def rWinning (G : BCSGame) (d : ℕ) : CPoly := by
  classical
  exact total (enumFin G.contexts) fun c => total (enumFin G.numVars) fun w =>
    cmul (cconst (G.probability c w)) (csum ((G.allowed c).toList.map fun a =>
      rTotal₂ d fun i j => rTotal₂ d fun k l =>
        cmul (rR G false i j k l) (cmul (rA G false c a k i) (rB G false w (a w) l j))))

def rConstraints (G : BCSGame) (eps : ℚ) (d : ℕ) : Sentence :=
  rAll₂ d (fun i j => rAll₂ d fun k l => ceq (rR G false i j k l) (rRGram G d true i j k l)) ++
  ceq (rTotal₂ d fun i j => rR G false i j i j) cone ++
  all (enumFin G.contexts) (fun c =>
    all (enumFixed (Fin G.numVars → Bool)) (fun a => rEq d (rA G false c a) (rGram d (rA G true c a))) ++
    rEq d (fun i j => total (enumFixed (Fin G.numVars → Bool)) fun a => rA G false c a i j) rIdentity) ++
  all (enumFin G.numVars) (fun w =>
    all (enumFixed Bool) (fun b => rEq d (rB G false w b) (rGram d (rB G true w b))) ++
    rEq d (fun i j => total (enumFixed Bool) fun b => rB G false w b i j) rIdentity) ++
  [(false,sub (constant eps) (sub (constant 1) (rWinning G d).1))]

def rSentence (G : BCSGame) (eps : ℚ) (d : ℕ) : Sentence :=
  if d=0 then [(false,constant (-1))] else rConstraints G eps d

theorem map_finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem all_fin_raw (n : ℕ) (f : ℕ → Sentence) : all (enumFin n) (fun i => f i.val) = rAll n f := by
  unfold all enumFin rAll
  rw [← map_finRange_val n,List.flatMap_map]

theorem total_fin_raw (n : ℕ) (f : ℕ → CPoly) : total (enumFin n) (fun i => f i.val) = rTotal n f := by
  unfold total enumFin rTotal
  rw [← map_finRange_val n,List.map_map]
  rfl

@[simp] theorem csum_append (xs ys : List CPoly) : csum (xs++ys) = cadd (csum xs) (csum ys) := by
  simp [csum,cadd,add,sum]

theorem csum_flatMap {α : Type*} (xs : List α) (f : α → List CPoly) :
    csum (xs.flatMap f) = csum (xs.map fun x => csum (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,csum_append,List.map_cons]
    change cadd (csum (f x)) (csum (xs.flatMap f)) = cadd (csum (f x)) (csum (xs.map _))
    rw [ih]

theorem all_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (E : Enumeration ι) (F : Enumeration κ)
    (f : ι × κ → Sentence) : all (enumProd E F) f = all E fun i => all F fun j => f (i,j) := by
  simp [all,enumProd,List.flatMap_assoc,List.flatMap_map]
theorem total_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (E : Enumeration ι) (F : Enumeration κ)
    (f : ι × κ → CPoly) : total (enumProd E F) f = total E fun i => total F fun j => f (i,j) := by
  simp [total,enumProd,List.map_flatMap,List.map_map,csum_flatMap,Function.comp_def]

theorem symbols_rR (G : BCSGame) (d : ℕ) (b : Bool) (i j : Fin d × Fin d) :
    (symbols G d b).rho i j = rR G b i.1 i.2 j.1 j.2 := rfl
theorem symbols_rA (G : BCSGame) (d : ℕ) (b : Bool) (c : Fin G.contexts)
    (a : Fin G.numVars → Bool) (i j : Fin d) : (symbols G d b).alice c a i j = rA G b c a i j := rfl
theorem symbols_rB (G : BCSGame) (d : ℕ) (b : Bool) (w : Fin G.numVars)
    (a : Bool) (i j : Fin d) : (symbols G d b).bob w a i j = rB G b w a i j := rfl

theorem all_fin_compare {n : ℕ} {f : Fin n → Sentence} {g : ℕ → Sentence}
    (h : ∀ i, f i = g i.val) : all (enumFin n) f = rAll n g := by
  rw [← all_fin_raw]
  congr 1
  funext i; exact h i

theorem total_fin_compare {n : ℕ} {f : Fin n → CPoly} {g : ℕ → CPoly}
    (h : ∀ i, f i = g i.val) : total (enumFin n) f = rTotal n g := by
  rw [← total_fin_raw]
  congr 1
  funext i; exact h i

open Lean Elab Tactic in
elab "raw_step" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let some (_,lhs,rhs) := t.eq? | throwError "expected equality"
  if lhs.getAppFn.constName? == some ``all && rhs.getAppFn.constName? == some ``rAll then
    evalTactic (← `(tactic| apply all_fin_compare; intro i))
  else if lhs.getAppFn.constName? == some ``total && rhs.getAppFn.constName? == some ``rTotal then
    evalTactic (← `(tactic| apply total_fin_compare; intro i))
  else
    evalTactic (← `(tactic| first | with_reducible rfl | funext i | congr 1))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 300000 in
theorem sentence_eq_raw (G : BCSGame) (eps : ℚ) (d : ℕ) : sentence G eps d = rSentence G eps d := by
  classical
  unfold sentence rSentence
  congr 1
  simp only [constraints,rConstraints,lossPoly,winningPoly,matrixEq,gram,tr,all_prod,total_prod,
    symbols_rR,symbols_rA,symbols_rB]
  simp only [rAll₂,rTotal₂,rEq,rGram,rRGram,rWinning,identity,rIdentity]
  simp only [Fin.ext_iff]
  repeat' raw_step


end
end E2.FeasibilitySentence
