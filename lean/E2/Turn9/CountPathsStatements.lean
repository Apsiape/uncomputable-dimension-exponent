import E2.Turn9.CountStatements

namespace E2.Turn9
noncomputable section
open scoped BigOperators

def movedWord {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m) (a : RecordType p) : Mat d :=
  (p i).projection (a i)*
    (((List.finRange m).filter (fun j => j≠i)).map (fun j => (p j).projection (a j))).prod

/-- Planned lemma suffix_swap_vector: the all-branch vector estimate before
passing to variation distance. The suffix has i's measurement in slot zero. -/
def SuffixSwapVector : Prop := ∃ C : ℝ, 0<C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d) (u : Fin m → Mat d),
  0≤η → TriangularRelations s η p u → ∀ i : Fin m,
    Recording.familyNorm (fun a : RecordType (suffix p i.val) =>
      reverseWord (suffix p i.val) (swapRecord (suffix p i.val) ⟨0,by omega⟩ a)*s.xi-
        u i*(reverseWord (suffix p i.val) a*s.xi)*(u i).conjTranspose)≤C*m^2*η

/-- Planned lemma move_to_end_vector: adjacent swaps with the original label
record fixed; no change of Hilbert space and no branch normalization. -/
def MoveToEndVector : Prop := ∃ C : ℝ, 0<C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d),
  0≤η → (∀ i a, hs (comm ((p i).projection a) s.xi)≤η) →
  (∀ i j, i≠j → ∀ a b, weighted s (comm ((p i).projection a) ((p j).projection b))≤η) →
  ∀ i : Fin m, Recording.familyNorm (fun a : RecordType p =>
    (reverseWord p a-movedWord p i a)*s.xi)≤C*m^2*η

end
end E2.Turn9
