import E2.FiniteWordNumber
import E2.FiniteSlotBound
import E2.FiniteOptionalMatrices
import E2.FiniteDecodeResetFunctions
import E2.FiniteHistoryFunctions

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem listRotate_length (bs : List Bool) : (listRotate bs).length=bs.length := by
  cases bs <;> simp [listRotate]

theorem listRotateBack_rotate (bs : List Bool) : listRotateBack (listRotate bs)=bs := by
  cases bs with
  | nil => rfl
  | cons b bs => exact listRotateBack_append bs b

theorem listRotate_rotateBack (bs : List Bool) : listRotate (listRotateBack bs)=bs := by
  cases hr : bs.reverse with
  | nil =>
    have he := congrArg List.reverse hr
    simp only [List.reverse_reverse,List.reverse_nil] at he
    subst bs
    rfl
  | cons b cs =>
    have he := congrArg List.reverse hr
    simp only [List.reverse_reverse,List.reverse_cons] at he
    rw [he,listRotateBack_append]
    rfl

theorem listRotateBack_length (bs : List Bool) : (listRotateBack bs).length=bs.length := by
  rw [←listRotate_length (listRotateBack bs),listRotate_rotateBack]

def rotateBinary (N : ℕ) : Equiv.Perm (BinaryWord N) where
  toFun b := ⟨listRotate b.val,(listRotate_length b.val).trans b.property⟩
  invFun b := ⟨listRotateBack b.val,(listRotateBack_length b.val).trans b.property⟩
  left_inv b := Subtype.ext (listRotateBack_rotate b.val)
  right_inv b := Subtype.ext (listRotate_rotateBack b.val)

/-- First nonzero base-four digit: its position and whether its value is one. -/
def binaryDecode : List Bool → Option (ℕ × Bool)
  | [] => none
  | [_] => none
  | b::c::bs => if b || c then some (0,b && !c)
      else (binaryDecode bs).map (fun z => (z.1+1,z.2))

def leadingOnes (bs : List Bool) : ℕ := (bs.takeWhile id).length

def decodedL (bs : List Bool) : Bool := ((binaryDecode bs).getD (0,false)).2

def decodedR (bs : List Bool) : ℝ :=
  match binaryDecode bs with
  | none => 0
  | some z => counterCoordinate z.1

def historyInitial (p : CounterProgram) (bs : List Bool) : Configuration p :=
  let z := (binaryDecode bs).getD (0,false)
  ⟨if z.2 then p.start else p.idle,(p.initial z.1).counter⟩

def historyConfig (p : CounterProgram) (bs qs ts : List Bool) : Configuration p :=
  cyclicHistory p.step (historyInitial p bs) (2^leadingOnes qs) (listNumber ts)

def historyR (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) : ℝ :=
  if binaryDecode bs=none ∧ i.val=0 then 0
  else counterCoordinate ((historyConfig p bs qs ts).counter i)

def historyZ (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) : ℝ :=
  if binaryDecode bs=none ∧ i.val=0 then 0
  else counterZero ((historyConfig p bs qs ts).counter i)

def historyS (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) : ℝ :=
  if binaryDecode bs=none ∧ i.val=0 then 0
  else counterWitness ((historyConfig p bs qs ts).counter i)

abbrev SourceBasis (N k : ℕ) := (BinaryWord N × Bits k) × (BinaryWord N × BinaryWord N)

theorem binaryWord_card (N : ℕ) : Fintype.card (BinaryWord N)=2^N := by
  rw [Fintype.card_congr (Equiv.vectorEquivFin Bool N)]
  simp

theorem sourceBasis_card (N k : ℕ) : Fintype.card (SourceBasis N k)=2^(3*N+k) := by
  simp only [SourceBasis,Fintype.card_prod,binaryWord_card,Bits,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin]
  rw [show 3*N+k=(N+k)+(N+N) by omega,pow_add,pow_add,pow_add]

def sourceBasisEquiv (N k : ℕ) : Fin (2^(3*N+k)) ≃ SourceBasis N k :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin,sourceBasis_card])

def sourcePerm (N k : ℕ) (s : Equiv.Perm (SourceBasis N k)) :
    Equiv.Perm (Fin (2^(3*N+k))) :=
  (sourceBasisEquiv N k).trans (s.trans (sourceBasisEquiv N k).symm)

def sourceDiagonal (N k : ℕ) (a : SourceBasis N k → ℝ) : Mat (2^(3*N+k)) :=
  Matrix.diagonal (fun i => (a (sourceBasisEquiv N k i):ℂ))

def addressLift {N k : ℕ} (s : Equiv.Perm (BinaryWord N × Bits k)) : Equiv.Perm (SourceBasis N k) :=
  s.prodCongr (Equiv.refl _)

def fuelLift {N k : ℕ} (s : Equiv.Perm (BinaryWord N)) : Equiv.Perm (SourceBasis N k) :=
  (Equiv.refl _).prodCongr (s.prodCongr (Equiv.refl _))

def timeLift {N k : ℕ} (s : Equiv.Perm (BinaryWord N)) : Equiv.Perm (SourceBasis N k) :=
  (Equiv.refl _).prodCongr ((Equiv.refl _).prodCongr s)

def wordMask (p : CounterProgram) (N : ℕ) (b : BinaryWord N) : Bool :=
  finiteMask p N (listNumber b.val)

def addressDressing (p : CounterProgram) (N k : ℕ) : Equiv.Perm (BinaryWord N × Bits k) :=
  dressing (rotateWord k).symm (fun b => flagPrefix (finiteMask p N) (listNumber b.val))

def addressForward (p : CounterProgram) (N k : ℕ) : Equiv.Perm (BinaryWord N × Bits k) :=
  skewShift (incrementWord N) (rotateWord k).symm (fun b => if wordMask p N b then 1 else 0)

def addressRotation (p : CounterProgram) (N k : ℕ) : Equiv.Perm (BinaryWord N × Bits k) :=
  (addressDressing p N k).symm.trans
    (((rotateBinary N).prodCongr (Equiv.refl _)).trans (addressDressing p N k))

def addressFlip (p : CounterProgram) (N k : ℕ) : Equiv.Perm (BinaryWord N × Bits k) :=
  (addressDressing p N k).symm.trans
    (((flipFirstWord N).prodCongr (Equiv.refl _)).trans (addressDressing p N k))

def sourceCore (p : CounterProgram) (N : ℕ) (n : ℕ) : Mat (2^(3*N+finiteSlots p N)) :=
  let k := finiteSlots p N
  haveI : NeZero k := ⟨Nat.ne_of_gt (finiteSlots_pos p N)⟩
  let d := sourceDiagonal N k
  let m := fun s => (sourcePerm N k s).permMatrix ℂ
  match n with
  | 0 => d (fun z => listCoordinate z.1.1.val)
  | 1 => d (fun z => boolValue (z.1.1.val.headD false))
  | 2 => m (addressLift (addressRotation p N k))
  | 3 => m (addressLift (addressFlip p N k))
  | 4 => d (fun z => listCoordinate z.2.1.val)
  | 5 => d (fun z => boolValue (z.2.1.val.headD false))
  | 6 => m (fuelLift (rotateBinary N))
  | 7 => m (fuelLift (flipFirstWord N))
  | 8 => d (fun z => listCoordinate z.2.2.val)
  | 9 => d (fun z => boolValue (z.2.2.val.headD false))
  | 10 => m (timeLift (rotateBinary N))
  | 11 => m (timeLift (flipFirstWord N))
  | 12 => m (addressLift (addressForward p N k).symm)
  | 13 => m (timeLift (incrementWord N).symm)
  | 14 => d (fun z => listCarry z.1.1.val)
  | 15 => d (fun z => boolValue (decodedL z.1.1.val))
  | 16 => d (fun z => decodedR z.1.1.val)
  | 17 => d (fun z => boolValue (listReset z.2.1.val z.2.2.val))
  | 18 => d (fun z => optionalFlag (wordMask p N) z.1)
  | 19 => d (fun z => permutationSeries (optionalBackward (incrementWord N) (wordMask p N))
      (optionalDigit (wordMask p N)) z.1)
  | 20 => d (fun z => permutationSeries (optionalBackward (incrementWord N) (wordMask p N))
      (optionalFlag (wordMask p N)) z.1)
  | 21 => d (fun z => optionalDigit (wordMask p N) z.1)
  | 22 => m (addressLift (optionalFlip (wordMask p N)))
  | _ => 0

/-- One explicit assignment on the required common dimension. This definition
alone does not assert the domain or source-relation obligations. -/
def sourceTuple (p : CounterProgram) (N : ℕ) : SourceVar p → Mat (2^(3*N+finiteSlots p N)) :=
  fun j =>
  if hcore : j.val < 23 then sourceCore p N j.val
  else if hc : j.val < 23+3*p.counters then
    let i : Fin p.counters := ⟨(j.val-23)/3,by omega⟩
    sourceDiagonal N (finiteSlots p N) (fun z =>
      match (j.val-23)%3 with
      | 0 => historyR p z.1.1.val z.2.1.val z.2.2.val i
      | 1 => historyZ p z.1.1.val z.2.1.val z.2.2.val i
      | _ => historyS p z.1.1.val z.2.1.val z.2.2.val i)
  else
    let q : Fin p.controls := ⟨j.val-(23+3*p.counters),by have := j.isLt; unfold sourceSize at this; omega⟩
    sourceDiagonal N (finiteSlots p N) (fun z =>
      if q=(historyConfig p z.1.1.val z.2.1.val z.2.2.val).control then 1 else 0)

theorem sourceTuple_exponent_bound (p : CounterProgram) (N : ℕ) (hN : 2 ≤ N) :
    |(finiteSlots p N:ℝ)-(∑' e, cutoff p N e)*N| ≤ 4*Real.logb 2 (N+2) := by
  rw [←maskDensity_eq_cutoff,mul_comm (maskDensity _)]
  exact finiteSlots_logb_bound p N hN

end
end E2.FiniteConstruction