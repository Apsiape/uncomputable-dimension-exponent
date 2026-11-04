import E2.CompilerUpperBase
import E2.CompilerCommonGadgets

namespace E2.CompilerUpper
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerBlocks E2.CompilerTensor E2.FiniteConstruction
open E2.CompilerFrontend Companion.Analytic
variable {ι : Type*} {d : ℕ}

abbrev GadgetKey (P : Presentation ι) := (r : Fin P.relations.length) × Fin (q P r+steps P r)

def baseWire (P : Presentation ι) (s : ι × Fin 2 → Mat d) : Wire P → Mat (registerSize P*d)
  | .inl _ => 1
  | .inr (.inl j) => baseSource P s j
  | .inr (.inr ⟨r,.inl (i,j)⟩) => ![baseX P r i,baseZ P r i,-baseZ P r i] j
  | .inr (.inr ⟨r,.inr (.inl _)⟩) => baseE P r
  | .inr (.inr ⟨r,.inr (.inr (.inl i))⟩) => baseControl P s r i
  | .inr (.inr ⟨r,.inr (.inr (.inr (.inl i)))⟩) => baseConjugate P s r (i.val+1)
  | .inr (.inr ⟨_,.inr (.inr (.inr (.inr _)))⟩) => 1

theorem baseWire_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (w : Wire P) : Domain.reflection.Holds (baseWire P s w) := by
  rcases w with u | (j | ⟨r,v⟩)
  · exact ⟨by simp [baseWire],by simp [baseWire]⟩
  · exact source_reflection _ (hs j)
  · rcases v with ⟨i,j⟩ | (u | (i | (i | ij)))
    · fin_cases j
      · exact baseX_domain P r i
      · exact baseZ_domain P r i
      · exact negative_reflection _ (baseZ_domain P r i)
    · exact baseE_domain P r
    · exact baseControl_domain P s hs r i
    · exact baseConjugate_domain P s hs r _
    · exact ⟨by simp [baseWire],by simp [baseWire]⟩

def gadgetTriple (P : Presentation ι) (s : ι × Fin 2 → Mat d) (k : GadgetKey P) : Fin 3 → Mat (registerSize P*d) :=
  Fin.addCases (fun i => ![baseX P k.1 i,baseZ P k.1 i,-baseZ P k.1 i])
    (fun i => ![baseControl P s k.1 i.rev,baseConjugate P s k.1 i.val,baseConjugate P s k.1 (i.val+1)]) k.2

theorem gadgetTriple_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (k : GadgetKey P) (j : Fin 3) :
    Domain.reflection.Holds (gadgetTriple P s k j) := by
  rcases k with ⟨r,k⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simp only [gadgetTriple,Fin.addCases_left]
    fin_cases j
    · exact baseX_domain P r i
    · exact baseZ_domain P r i
    · exact negative_reflection _ (baseZ_domain P r i)
  · simp only [gadgetTriple,Fin.addCases_right]
    fin_cases j
    · exact baseControl_domain P s hs r _
    · exact baseConjugate_domain P s hs r _
    · exact baseConjugate_domain P s hs r _

theorem gadgetTriple_conjugacy (P : Presentation ι) (s : ι × Fin 2 → Mat d) (k : GadgetKey P) :
    gadgetTriple P s k 0*gadgetTriple P s k 1*gadgetTriple P s k 0=gadgetTriple P s k 2 := by
  rcases k with ⟨r,k⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · simpa [gadgetTriple] using baseXZ_conjugate (d:=d) P r i i
  · simpa [gadgetTriple] using (baseConjugate_succ P s r i).symm

def auxiliaryPort (P : Presentation ι) : Wire P → Option (GadgetKey P × GadgetWire)
  | .inr (.inr ⟨r,.inr (.inr (.inr (.inr (i,j))))⟩) => some (⟨r,i⟩,j)
  | _ => none

def wireValue (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (aux : GadgetKey P → GadgetWire → Mat (2*(2*(registerSize P*d)))) (w : Wire P) : Mat (2*(2*(registerSize P*d))) :=
  match auxiliaryPort P w with
  | some (k,j) => aux k j
  | none => duplicate (duplicate (baseWire P s w))

@[simp] theorem wireValue_source (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (j) :
    wireValue P s aux (E2.CompilerNetwork.source P j)=duplicate (duplicate (baseSource P s j)) := rfl
@[simp] theorem wireValue_auxiliary (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) (j) :
    wireValue P s aux (auxiliary P r i j)=aux ⟨r,i⟩ j := rfl

theorem wireValue_domain (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ j, Domain.reflection.Holds (s j)) (aux)
    (haux : ∀ k j, Domain.reflection.Holds (aux k j)) (w) : Domain.reflection.Holds (wireValue P s aux w) := by
  unfold wireValue
  cases he : auxiliaryPort P w with
  | none => exact duplicate_domain _ _ (duplicate_domain _ _ (baseWire_domain P s hs w))
  | some kj => exact haux kj.1 kj.2

@[simp] theorem wireValue_X (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) :
    wireValue P s aux (X P r i)=duplicate (duplicate (baseX P r i)) := rfl
@[simp] theorem wireValue_Z (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) :
    wireValue P s aux (Z P r i)=duplicate (duplicate (baseZ P r i)) := rfl
@[simp] theorem wireValue_negZ (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) :
    wireValue P s aux (negZ P r i)=duplicate (duplicate (-baseZ P r i)) := rfl
@[simp] theorem wireValue_E (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) :
    wireValue P s aux (E P r)=duplicate (duplicate (baseE P r)) := rfl
@[simp] theorem wireValue_control (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) :
    wireValue P s aux (control P r i)=duplicate (duplicate (baseControl P s r i)) := rfl
@[simp] theorem wireValue_conjugate (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (r) (i) :
    wireValue P s aux (E2.CompilerNetwork.conjugate P r i)=duplicate (duplicate (baseConjugate P s r (i.val+1))) := rfl

def previousWire (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (steps P r)) : Wire P :=
  if h : i.val=0 then E P r else E2.CompilerNetwork.conjugate P r ⟨i.val-1,by omega⟩

theorem baseWire_previous (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r) (i) :
    baseWire P s (previousWire P r i)=baseConjugate P s r i.val := by
  unfold previousWire
  split_ifs with h
  · rw [h]
    rfl
  · change baseConjugate P s r (i.val-1+1)=baseConjugate P s r i.val
    congr 1
    omega

def gadgetInputs (P : Presentation ι) (k : GadgetKey P) : Fin 3 → Wire P :=
  Fin.addCases (fun i => ![X P k.1 i,Z P k.1 i,negZ P k.1 i])
    (fun i => ![control P k.1 i.rev,previousWire P k.1 i,E2.CompilerNetwork.conjugate P k.1 i]) k.2

theorem wireValue_gadgetInputs (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux) (k : GadgetKey P) (j) :
    wireValue P s aux (gadgetInputs P k j)=duplicate (duplicate (gadgetTriple P s k j)) := by
  rcases k with ⟨r,k⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · fin_cases j <;> simp [gadgetInputs,gadgetTriple]
  · fin_cases j
    · simp [gadgetInputs,gadgetTriple]
    · simp only [gadgetInputs,gadgetTriple,Fin.addCases_right]
      change wireValue P s aux (previousWire P r i) = duplicate (duplicate (baseConjugate P s r i.val))
      unfold previousWire
      split_ifs with h
      · rw [wireValue_E,h]
        rfl
      · rw [wireValue_conjugate]
        have he : i.val-1+1=i.val := by omega
        simp only [he]
    · simp [gadgetInputs,gadgetTriple]

/-- Source polynomials retain their normalized flat norm through the selector
factor and both common gadget doublings, for any choices of the auxiliaries. -/
theorem wireValue_source_weighted (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hd : 0<d) (aux) (p : Poly (ι × Fin 2)) :
    weighted (flatState (2*(2*(registerSize P*d))) (by have := registerSize_pos P; positivity))
      (Poly.eval (fun j => wireValue P s aux (E2.CompilerNetwork.source P j)) p) =
      weighted (flatState d hd) (Poly.eval s p) := by
  simp only [wireValue_source]
  rw [eval_duplicate,eval_duplicate]
  change weighted _ (duplicate (duplicate (Poly.eval (fun j => E2.CompilerTensor.source (registerSize P) (s j)) p))) = _
  rw [eval_source,weighted_duplicate (by have := registerSize_pos P; positivity),
    weighted_duplicate (Nat.mul_pos (registerSize_pos P) hd),weighted_source (registerSize_pos P) hd]

/-- All actual gadget ports, including every disjoint auxiliary label, share
one assignment in dimension 4*(registerSize P*d). Source norms are transported
by `wireValue_source_weighted`; all state commutators vanish on its flat state. -/
theorem upper_wire_extension (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hd : 0<d) (hs : ∀ j, Domain.reflection.Holds (s j)) :
    ∃ aux : GadgetKey P → GadgetWire → Mat (2*(2*(registerSize P*d))),
      (∀ w, Domain.reflection.Holds (wireValue P s aux w)) ∧
      (∀ k, GeneralData (fun i => duplicate (duplicate (gadgetTriple P s k i))) (fun j => aux k (.inl j))) ∧
      (∀ k i, SixData (subA (fun j => aux k (.inl j)) i)
        (subB (fun j => aux k (.inl j)) i) (subC (fun j => aux k (.inl j)) i)
        (fun j => aux k (.inr (i,j)))) ∧
      (∀ w, ‖wireValue P s aux w‖ ≤ 1) ∧
      (∀ w, comm (wireValue P s aux w)
        (flatState (2*(2*(registerSize P*d))) (by have := registerSize_pos P; positivity)).xi=0) := by
  obtain ⟨aux,haux,hgen,hsix⟩ := simultaneous_conjugacy_extension
    (gadgetTriple P s) (gadgetTriple_domain P s hs) (gadgetTriple_conjugacy P s)
  have hdom := wireValue_domain P s hs aux haux
  have hD : 0<2*(2*(registerSize P*d)) := by have := registerSize_pos P; positivity
  exact ⟨aux,hdom,hgen,hsix,fun w => reflection_norm hD _ (hdom w),fun w => flatState_commutes hD _⟩

end
end E2.CompilerUpper
