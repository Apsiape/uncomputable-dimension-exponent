import E2.CompilerRealize
import E2.CompilerWords

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize

/-- A local ordinary Boolean table, including its nonemptiness witness. -/
structure Table (V : Type*) [Fintype V] where
  scope : Finset V
  accepts : (V → Bool) → Prop
  locality : ∀ a b, (∀ v ∈ scope, a v=b v) → (accepts a ↔ accepts b)
  witness : ∃ a, accepts a

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V

def free (s : Finset V) : Table V :=
  ⟨s,fun _ => True,by simp,⟨fun _ => true,True.intro⟩⟩

def parity (a b c : V) : Table V where
  scope := {a,b,c}
  accepts x := sign (x a)=sign (x b)*sign (x c)
  locality x y h := by simp only [h a (by simp),h b (by simp),h c (by simp)]
  witness := ⟨fun _ => true,by norm_num [sign]⟩

def orthogonal (a b : V) : Table V where
  scope := {a,b}
  accepts x := ¬ (x a=true ∧ x b=true)
  locality x y h := by simp only [h a (by simp),h b (by simp)]
  witness := ⟨fun _ => false,by simp⟩

def functional (s : Finset V) (out : V) (fresh : out ∉ s)
    (f : (V → Bool) → Bool)
    (hf : ∀ a b, (∀ v ∈ s, a v=b v) → f a=f b) : Table V where
  scope := insert out s
  accepts a := a out=f a
  locality a b h := by
    rw [h out (by simp),hf a b (fun v hv => h v (Finset.mem_insert_of_mem hv))]
  witness := by
    classical
    let a : V → Bool := Function.update (fun _ => true) out (f (fun _ => true))
    refine ⟨a,?_⟩
    have he : f a=f (fun _ => true) := hf _ _ (fun v hv => by
      simp [a,Function.update_of_ne (show v ≠ out from fun h => fresh (h ▸ hv))])
    simp [a,he]

def andTable (out : V) (xs : Finset V) : Table V where
  scope := insert out xs
  accepts a := a out=true ↔ ∀ v ∈ xs, a v=true
  locality a b h := by
    rw [h out (by simp)]
    exact iff_congr Iff.rfl (forall₂_congr (fun v hv => by rw [h v (by simp [hv])]))
  witness := ⟨fun _ => true,by simp⟩

/-- A complete conjugacy gadget: seven parity contexts and four six-context
subgadgets. No conjugacy is left as a non-Boolean relation. -/
abbrev GadgetWire := Fin 11 ⊕ (Fin 4 × Fin 7)

def sixTables (a b c : V) (d : Fin 7 → V) : List (Table V) :=
  [parity a (d 0) (d 1),parity b (d 1) (d 2),parity (d 2) (d 3) (d 4),
   parity a (d 4) (d 5),parity c (d 5) (d 6),parity (d 0) (d 3) (d 6)]

def conjugacyTables (a b c : V) (aux : GadgetWire → V) : List (Table V) :=
  let x : Fin 3 → V := ![a,b,c]
  let f := aux (.inl 0)
  let g := aux (.inl 1)
  let y : Fin 3 → V := fun i => aux (.inl ⟨2+i.val,by omega⟩)
  let z : Fin 3 → V := fun i => aux (.inl ⟨5+i.val,by omega⟩)
  let w : Fin 3 → V := fun i => aux (.inl ⟨8+i.val,by omega⟩)
  (List.finRange 3).map (fun i => parity (x i) (y i) (z i)) ++
  (List.finRange 3).map (fun i => parity (x i) f (w i)) ++ [parity g (y 1) (z 2)] ++
  (List.finRange 3).flatMap (fun i => sixTables f (y i) (z i)
    (fun j => aux (.inr (i.castSucc,j)))) ++
  sixTables (w 0) (y 1) (z 2) (fun j => aux (.inr (3,j)))

/-- Transport a finite symbolic variable set to the game's required Fin labels. -/
def Table.relabel (t : Table V) : Table (Fin (Fintype.card V)) where
  scope := t.scope.image (Fintype.equivFin V)
  accepts a := t.accepts (fun v => a (Fintype.equivFin V v))
  locality a b h := t.locality _ _ (fun v hv => h _ (Finset.mem_image_of_mem _ hv))
  witness := by
    obtain ⟨a,ha⟩ := t.witness
    exact ⟨fun v => a ((Fintype.equivFin V).symm v),by simpa using ha⟩

def game [Nonempty V] (ts : List (Table V)) : BCSGame := by
  classical
  let extra : Table (Fin (Fintype.card V)) := free {0}
  let table : Fin (ts.length+1) → Table (Fin (Fintype.card V)) :=
    Fin.cases extra (fun i => (ts.get i).relabel)
  apply CompilerGame.uniform (fun c => (table c).scope)
    (fun c => Finset.univ.filter (table c).accepts)
  · intro c
    obtain ⟨a,ha⟩ := (table c).witness
    exact ⟨a,by simp [ha]⟩
  · intro c a b h
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (table c).locality a b h
  · have h := Finset.single_le_sum (fun c (_ : c ∈ (Finset.univ : Finset (Fin (ts.length+1)))) =>
        Nat.zero_le ((table c).scope.card)) (Finset.mem_univ (0 : Fin (ts.length+1)))
    have he : (table (0 : Fin (ts.length+1))).scope.card=1 := by simp [table,extra,free]
    dsimp [CompilerGame.incidenceCount]
    omega

/-- Integer signed-word packing, with a power-of-two slot count. The subsequent
normalization theorem must connect these slots to the source polynomial. -/
def denominator {κ : Type*} (ws : CompilerWords.WordSum κ) : ℕ :=
  (ws.map (fun t => t.1.den)).prod

def signedWords {κ : Type*} (ws : CompilerWords.WordSum κ) : List (Bool × List κ) :=
  ws.flatMap (fun t =>
    let z : ℤ := ((denominator ws : ℤ)*t.1.num) / (t.1.den : ℤ)
    List.replicate (2*z.natAbs) (decide (0 ≤ z),t.2))

def selectorCount {κ : Type*} (ws : CompilerWords.WordSum κ) : ℕ :=
  Nat.clog 2 ((signedWords ws).length+2)

def packedWords {κ : Type*} (ws : CompilerWords.WordSum κ) : List (Bool × List κ) :=
  let raw := signedWords ws
  let pairs := (2^(selectorCount ws)-raw.length)/2
  raw ++ List.replicate pairs (true,[]) ++ List.replicate pairs (false,[])

structure Letter (κ : Type*) (q : ℕ) where
  selector : Fin q → Bool
  source : Option κ
  positive : Bool

def letters {κ : Type*} (ws : CompilerWords.WordSum κ) : List (Letter κ (selectorCount ws)) :=
  (Finset.univ : Finset (Fin (selectorCount ws) → Bool)).toList.flatMap (fun a =>
    let t := (packedWords ws).getD ((Fintype.equivFin _ a).val) (true,[])
    ⟨a,none,t.1⟩ :: t.2.map (fun s => ⟨a,some s,true⟩))

variable {ι : Type*} [Fintype ι]

def relationWords (P : Presentation ι) (r : Fin P.relations.length) :
    CompilerWords.WordSum (ι × Fin 2) :=
  CompilerWords.normalForm (CompilerFrontend.substitute (CompilerFrontend.replacement P)
    (P.relations.get r))

def q (P : Presentation ι) (r : Fin P.relations.length) := selectorCount (relationWords P r)
def steps (P : Presentation ι) (r : Fin P.relations.length) := (letters (relationWords P r)).length

/-- Per-relation wires: X/Z/negative-Z, E, controls, successive conjugates,
and disjoint auxiliaries for every Pauli and word conjugacy gadget. -/
abbrev RelationWire (P : Presentation ι) (r : Fin P.relations.length) :=
  (Fin (q P r) × Fin 3) ⊕ (Unit ⊕ (Fin (steps P r) ⊕
    (Fin (steps P r) ⊕ (Fin (q P r + steps P r) × GadgetWire))))

abbrev Wire (P : Presentation ι) := Unit ⊕ ((ι × Fin 2) ⊕
  (r : Fin P.relations.length) × RelationWire P r)

instance wireNonempty (P : Presentation ι) : Nonempty (Wire P) := ⟨.inl ()⟩

def source (P : Presentation ι) (s : ι × Fin 2) : Wire P := .inr (.inl s)
def localWire (P : Presentation ι) (r : Fin P.relations.length) (v : RelationWire P r) : Wire P :=
  .inr (.inr ⟨r,v⟩)
def X (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) : Wire P :=
  localWire P r (.inl (i,0))
def Z (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) : Wire P :=
  localWire P r (.inl (i,1))
def negZ (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) : Wire P :=
  localWire P r (.inl (i,2))
def E (P : Presentation ι) (r : Fin P.relations.length) : Wire P :=
  localWire P r (.inr (.inl ()))
def control (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (steps P r)) : Wire P :=
  localWire P r (.inr (.inr (.inl i)))
def conjugate (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (steps P r)) : Wire P :=
  localWire P r (.inr (.inr (.inr (.inl i))))
def auxiliary (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r + steps P r)) (j : GadgetWire) : Wire P :=
  localWire P r (.inr (.inr (.inr (.inr (i,j)))))

def F (P : Presentation ι) (r : Fin P.relations.length) : Wire P :=
  if h : steps P r=0 then E P r else conjugate P r ⟨steps P r-1,by omega⟩

def controlTable (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (steps P r)) : Table (Wire P) := by
  classical
  let t := (letters (relationWords P r)).get i
  let ins : Finset (Wire P) := Finset.univ.image (Z P r) ∪
    (t.source.toList.map (source P)).toFinset
  let f : (Wire P → Bool) → Bool := fun a =>
    if ∀ j, a (Z P r j)=t.selector j then
      if t.positive then t.source.elim true (fun s => a (source P s))
      else !(t.source.elim true (fun s => a (source P s)))
    else true
  refine functional ins (control P r i) ?_ f ?_
  · simp [ins,control,Z,source,localWire]
  · intro a b h
    have hz (j) : a (Z P r j)=b (Z P r j) := h _ (by simp [ins])
    have hs (s) (ht : t.source=some s) : a (source P s)=b (source P s) :=
      h _ (by simp [ins,ht])
    dsimp [f]
    simp_rw [hz]
    cases ht : t.source with
    | none => rfl
    | some s => simp only [Option.elim_some,hs s ht]

def relationTables (P : Presentation ι) (r : Fin P.relations.length) : List (Table (Wire P)) := by
  classical
  exact
    -- The AND and the two-variable orthogonality contexts remain separate.
    [andTable (E P r) (Finset.univ.image (X P r)),orthogonal (E P r) (F P r)] ++
    -- Only commuting selector/source families occur in free contexts.
    [free (Finset.univ.image (X P r)),free (Finset.univ.image (Z P r))] ++
    (Finset.univ : Finset ((ι × Fin 2) × Fin (q P r))).toList.flatMap (fun si =>
      [free {source P si.1,X P r si.2},free {source P si.1,Z P r si.2}]) ++
    (Finset.univ : Finset (Fin (q P r) × Fin (q P r))).toList.flatMap (fun ij =>
      if ij.1=ij.2 then [] else [free {X P r ij.1,Z P r ij.2}]) ++
    (List.finRange (q P r)).flatMap (fun j =>
      [functional {Z P r j} (negZ P r j) (by simp [negZ,Z,localWire])
        (fun a => !(a (Z P r j))) (by intro a b h; rw [h _ (by simp)])] ++
      conjugacyTables (X P r j) (Z P r j) (negZ P r j)
        (auxiliary P r ⟨j.val,by have := j.isLt; omega⟩)) ++
    (List.finRange (steps P r)).map (controlTable P r) ++
    (List.finRange (steps P r)).flatMap (fun j =>
      let previous := if h : j.val=0 then E P r else conjugate P r ⟨j.val-1,by omega⟩
      conjugacyTables (control P r j.rev) previous (conjugate P r j)
        (auxiliary P r ⟨q P r+j.val,by have := j.isLt; omega⟩))

def tables (P : Presentation ι) : List (Table (Wire P)) :=
  (List.finRange P.relations.length).flatMap (relationTables P)

/-- The concrete finite ordinary Boolean game for a source presentation.
It uses uniform positive rational incidence probabilities and all the Boolean
tables of the selector, controlled-word, and simultaneous conjugacy network. -/
abbrev realize (P : Presentation ι) : BCSGame := game (tables P)

end
end E2.CompilerNetwork
