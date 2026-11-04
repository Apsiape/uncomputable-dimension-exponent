import E2.CompilerDuplication
import E2.CompilerNetwork

namespace E2.CompilerBlocks
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.FiniteConstruction Companion.Analytic
variable {d : ℕ}
set_option maxHeartbeats 200000

def yIndex (i : Fin 3) : Fin 11 := ⟨2+i.val,by omega⟩
def zIndex (i : Fin 3) : Fin 11 := ⟨5+i.val,by omega⟩
def wIndex (i : Fin 3) : Fin 11 := ⟨8+i.val,by omega⟩

/-- Algebraic content of all seven primary parity contexts and all four
remaining commuting-target conjugacies, in the actual matrix type. -/
structure GeneralData (X : Fin 3 → Mat d) (g : Fin 11 → Mat d) : Prop where
  domains : ∀ j, Domain.reflection.Holds (g j)
  xyz : ∀ i, ParityTriple (X i) (g (yIndex i)) (g (zIndex i))
  xfw : ∀ i, ParityTriple (X i) (g 0) (g (wIndex i))
  gyz : ParityTriple (g 1) (g (yIndex 1)) (g (zIndex 2))
  conjugacy : ∀ i, g 0*g (yIndex i)*g 0=g (zIndex i)
  lastConjugacy : g (wIndex 0)*g (yIndex 1)*g (wIndex 0)=g (zIndex 2)
  targets : ∀ i, g (yIndex i)*g (zIndex i)=g (zIndex i)*g (yIndex i)
  lastTargets : g (yIndex 1)*g (zIndex 2)=g (zIndex 2)*g (yIndex 1)

/-- The displayed general gadget in dimension 2d. -/
theorem general_data_extension (X : Fin 3 → Mat d)
    (hX : ∀ i, Domain.reflection.Holds (X i)) (hrel : X 0*X 1*X 0=X 2) :
    ∃ g : Fin 11 → Mat (2*d), GeneralData (fun i => duplicate (X i)) g := by
  obtain ⟨hf,hg,hyzw,hxyz,hxfw,hgyz,hconj,hlast,htarget,hlastTarget⟩ :=
    general_extension X hX hrel
  let raw : Fin 11 → Block (Mat d) := ![off 1 1,diag (X 1) (X 2),
    generalY X 0,generalY X 1,generalY X 2,
    generalZ X 0,generalZ X 1,generalZ X 2,
    generalW X 0,generalW X 1,generalW X 2]
  let g : Fin 11 → Mat (2*d) := fun j => doubleMatrix (raw j)
  have hy (i : Fin 3) : g (yIndex i)=doubleMatrix (generalY X i) := by
    fin_cases i <;> rfl
  have hz (i : Fin 3) : g (zIndex i)=doubleMatrix (generalZ X i) := by
    fin_cases i <;> rfl
  have hw (i : Fin 3) : g (wIndex i)=doubleMatrix (generalW X i) := by
    fin_cases i <;> rfl
  refine ⟨g,?_⟩
  constructor
  · intro j
    apply doubleMatrix_reflection
    fin_cases j
    · exact hf
    · exact hg
    · exact (hyzw 0).1
    · exact (hyzw 1).1
    · exact (hyzw 2).1
    · exact (hyzw 0).2.1
    · exact (hyzw 1).2.1
    · exact (hyzw 2).2.1
    · exact (hyzw 0).2.2
    · exact (hyzw 1).2.2
    · exact (hyzw 2).2.2
  · intro i
    rw [hy,hz]
    exact doubleMatrix_parity _ _ _ (hxyz i)
  · intro i
    rw [hw]
    exact doubleMatrix_parity _ _ _ (hxfw i)
  · rw [hy,hz]
    exact doubleMatrix_parity _ _ _ hgyz
  · intro i
    rw [hy,hz]
    change doubleMatrix (off 1 1)*doubleMatrix (generalY X i)*doubleMatrix (off 1 1) = _
    rw [← doubleMatrix_mul,← doubleMatrix_mul,hconj]
  · rw [hw,hy,hz]
    rw [← doubleMatrix_mul,← doubleMatrix_mul,hlast]
  · intro i
    rw [hy,hz,← doubleMatrix_mul,← doubleMatrix_mul,htarget]
  · rw [hy,hz,← doubleMatrix_mul,← doubleMatrix_mul,hlastTarget]

def subA {n : ℕ} (g : Fin 11 → Mat n) : Fin 4 → Mat n := ![g 0,g 0,g 0,g (wIndex 0)]
def subB {n : ℕ} (g : Fin 11 → Mat n) : Fin 4 → Mat n := ![g (yIndex 0),g (yIndex 1),g (yIndex 2),g (yIndex 1)]
def subC {n : ℕ} (g : Fin 11 → Mat n) : Fin 4 → Mat n := ![g (zIndex 0),g (zIndex 1),g (zIndex 2),g (zIndex 2)]

/-- Six parity contexts, retaining every vertex and its original order. -/
def SixData {n : ℕ} (a b c : Mat n) (s : Fin 7 → Mat n) : Prop :=
  (∀ j, Domain.reflection.Holds (s j)) ∧
  ParityTriple a (s 0) (s 1) ∧ ParityTriple b (s 1) (s 2) ∧
  ParityTriple (s 2) (s 3) (s 4) ∧ ParityTriple a (s 4) (s 5) ∧
  ParityTriple c (s 5) (s 6) ∧ ParityTriple (s 0) (s 3) (s 6)

/-- All disjoint conjugacy gadgets may share two ancillary qubits: no context
compares auxiliaries of different gadgets. The overhead is four for any family. -/
theorem simultaneous_conjugacy_extension {κ : Type*} (X : κ → Fin 3 → Mat d)
    (hX : ∀ k i, Domain.reflection.Holds (X k i))
    (hrel : ∀ k, X k 0*X k 1*X k 0=X k 2) :
    ∃ aux : κ → GadgetWire → Mat (2*(2*d)),
      (∀ k j, Domain.reflection.Holds (aux k j)) ∧
      (∀ k, GeneralData (fun i => duplicate (duplicate (X k i))) (fun j => aux k (.inl j))) ∧
      (∀ k i, SixData
        (subA (fun j => aux k (.inl j)) i)
        (subB (fun j => aux k (.inl j)) i)
        (subC (fun j => aux k (.inl j)) i)
        (fun j => aux k (.inr (i,j)))) := by
  classical
  choose g hg using fun k => general_data_extension (X k) (hX k) (hrel k)
  have hlocal (k : κ) (i : Fin 4) :
      ∃ s : Fin 7 → Mat (2*(2*d)),
        SixData (duplicate (subA (g k) i)) (duplicate (subB (g k) i))
          (duplicate (subC (g k) i)) s := by
    have ha : Domain.reflection.Holds (subA (g k) i) := by fin_cases i <;> exact (hg k).domains _
    have hb : Domain.reflection.Holds (subB (g k) i) := by fin_cases i <;> exact (hg k).domains _
    have hc : Domain.reflection.Holds (subC (g k) i) := by fin_cases i <;> exact (hg k).domains _
    have hr : subA (g k) i*subB (g k) i*subA (g k) i=subC (g k) i := by
      fin_cases i
      · exact (hg k).conjugacy 0
      · exact (hg k).conjugacy 1
      · exact (hg k).conjugacy 2
      · exact (hg k).lastConjugacy
    have ht : subB (g k) i*subC (g k) i=subC (g k) i*subB (g k) i := by
      fin_cases i
      · exact (hg k).targets 0
      · exact (hg k).targets 1
      · exact (hg k).targets 2
      · exact (hg k).lastTargets
    exact six_extension_matrices _ _ _ ha hb hc hr ht
  choose s hs using hlocal
  let aux : κ → GadgetWire → Mat (2*(2*d)) := fun k j =>
    match j with
    | .inl j => duplicate (g k j)
    | .inr (i,j) => s k i j
  refine ⟨aux,?_,?_,?_⟩
  · intro k j
    cases j with
    | inl j => exact duplicate_domain _ _ ((hg k).domains j)
    | inr ij => exact (hs k ij.1).1 ij.2
  · intro k
    constructor
    · intro j; exact duplicate_domain _ _ ((hg k).domains j)
    · intro i; exact duplicate_parity _ _ _ ((hg k).xyz i)
    · intro i; exact duplicate_parity _ _ _ ((hg k).xfw i)
    · exact duplicate_parity _ _ _ (hg k).gyz
    · intro i; change duplicate _*duplicate _*duplicate _=duplicate _
      rw [← duplicate_mul,← duplicate_mul,(hg k).conjugacy]
    · change duplicate _*duplicate _*duplicate _=duplicate _
      rw [← duplicate_mul,← duplicate_mul,(hg k).lastConjugacy]
    · intro i; change duplicate _*duplicate _=duplicate _*duplicate _
      rw [← duplicate_mul,← duplicate_mul,(hg k).targets]
    · change duplicate _*duplicate _=duplicate _*duplicate _
      rw [← duplicate_mul,← duplicate_mul,(hg k).lastTargets]
  · intro k i
    fin_cases i <;> exact hs k _

end
end E2.CompilerBlocks
