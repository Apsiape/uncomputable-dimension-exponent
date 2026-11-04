import E2.MeasurementDefs

/-! Exact proof obligations for the Section 8 dependency graph. A definition
of a proposition is a specification, NOT a proof or a named hypothesis.
The original sole admission remains in E2/Measurements.lean. -/
namespace E2.Turn9
noncomputable section
open scoped BigOperators

def reverseWord {d m : ℕ} (p : Fin m → Measurement d) (a : RecordType p) : Mat d :=
  (List.ofFn (fun i => (p i).projection (a i))).prod

def recordMass {d m : ℕ} (s : State d) (p : Fin m → Measurement d)
    (a : RecordType p) : ℝ := hs (reverseWord p a * s.xi)^2

def recordEntropy {d m : ℕ} (s : State d) (p : Fin m → Measurement d) : ℝ :=
  (∑ a : RecordType p, Real.negMulLog (recordMass s p a)) / Real.log 2

def recordedActive {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  ∑ a : RecordType p, if a i = (p i).index 0 then 0 else recordMass s p a

def suffix {d m : ℕ} (p : Fin m → Measurement d) (i : ℕ) : Fin (m-i) → Measurement d :=
  fun j => p ⟨i+j.val, by omega⟩

def swapRecord {d m : ℕ} (p : Fin m → Measurement d) (i : Fin m)
    (a : RecordType p) : RecordType p := Function.update a i ((p i).swap (a i))

def swapVariation {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  (∑ a : RecordType p, |recordMass s p a - recordMass s p (swapRecord p i a)|) / 2

def decodeFailure {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  ∑ a : RecordType p, hs ((1-(p i).projection (a i))*reverseWord p a*s.xi)^2

/-- Planned lemma: suffix_swap_bound; it uses only the later-preservation direction. -/
def SuffixSwapBound : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d) (u : Fin m → Mat d),
  0 ≤ η → TriangularRelations s η p u →
  ∀ i : Fin m, swapVariation s (suffix p i.val) ⟨0, by omega⟩ ≤ C*m^2*η

/-- Planned lemma: active_probability_transport; all original-state expectations. -/
def ActiveProbabilityTransport : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d),
  0 ≤ η → (∀ i a, hs (comm ((p i).projection a) s.xi) ≤ η) →
  ∀ i : Fin m, (p i).outcomes = 3 →
    |recordedActive s p i - expectation s (p i).active| ≤ C*m*η

/-- Planned lemma: record_entropy_lower, from suffix swaps, chain rule and activation transport. -/
def RecordEntropyLower : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d) (u : Fin m → Mat d),
  0 ≤ η → TriangularRelations s η p u →
    binaryCount p + activeSum s p - C*m^3*η ≤ recordEntropy s p

/-- Planned lemma: decoder_error_bound, from adjacent swaps after arbitrary prefixes.
The failure projection acts on the ORIGINAL d-dimensional final system. -/
def DecoderErrorBound : Prop := ∃ C : ℝ, 0 < C ∧
  ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d),
  0 ≤ η → (∀ i a, hs (comm ((p i).projection a) s.xi) ≤ η) →
  (∀ i j, i ≠ j → ∀ a b, weighted s (comm ((p i).projection a) ((p j).projection b)) ≤ η) →
    ∀ i : Fin m, decodeFailure s p i ≤ C*m^4*η^2

/-- Planned lemma: record_information_upper, Holevo + conditional subadditivity +
Fano for a possibly correlated record, without conditioning on a branch. -/
def RecordInformationUpper : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d) (e : ℝ),
    0 < d → 0 ≤ e → e ≤ 1/2 → (∀ i, decodeFailure s p i ≤ e) →
    recordEntropy s p ≤ Real.logb 2 d + m*(binaryEntropy e+e)

end
end E2.Turn9
