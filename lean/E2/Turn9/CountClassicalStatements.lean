import E2.Turn9.CountStatements

namespace E2.Turn9
noncomputable section
open scoped BigOperators

def RecordNormalization : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d),
    (∀ a : RecordType p, 0≤recordMass s p a) ∧ (∑ a : RecordType p, recordMass s p a)=1

/-- Planned lemma classical_chain_lower: combines the exact entropy chain
rule and the proved binary/ternary imbalance inequalities. No operator premise. -/
def ClassicalChainLower : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d),
    binaryCount p + (∑ i∈Finset.univ.filter (fun i => (p i).outcomes=3),recordedActive s p i) -
      (∑ i : Fin m, swapVariation s (suffix p i.val) ⟨0,by omega⟩) ≤ recordEntropy s p

end
end E2.Turn9
