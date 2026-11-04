import E2.Turn9.CountStatements

/-! Fully concrete CQ information specifications. Conditional zero masses use
the original state as a totalization; their contribution is multiplied by zero.
No ensemble, entropy or Fano fact is assumed by these definitions. -/
namespace E2.Turn9
noncomputable section
open scoped BigOperators

def recordDensity {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) : Mat d :=
  reverseWord p a*s.rho*(reverseWord p a).conjTranspose

def finalDensity {d m : ℕ} (s : State d) (p : Fin m → Measurement d) : Mat d :=
  ∑ a : RecordType p, recordDensity s p a

def normalizedDensity {d : ℕ} (s : State d) (w : ℝ) (A : Mat d) : Mat d :=
  if w=0 then s.rho else ((w⁻¹:ℝ):ℂ) • A

def recordMeanEntropy {d m : ℕ} (s : State d) (p : Fin m → Measurement d) : ℝ :=
  ∑ a : RecordType p, recordMass s p a * Companion.Analytic.entropy
    (normalizedDensity s (recordMass s p a) (recordDensity s p a))

def marginalMass {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) (b : Fin (p i).outcomes) : ℝ :=
  ∑ a : RecordType p, if a i=b then recordMass s p a else 0

def marginalDensity {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) (b : Fin (p i).outcomes) : Mat d :=
  ∑ a : RecordType p, if a i=b then recordDensity s p a else 0

def marginalEntropy {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  (∑ b, Real.negMulLog (marginalMass s p i b))/Real.log 2

def marginalMeanEntropy {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  ∑ b, marginalMass s p i b * Companion.Analytic.entropy
    (normalizedDensity s (marginalMass s p i b) (marginalDensity s p i b))

def marginalConditionalEntropy {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (i : Fin m) : ℝ :=
  marginalEntropy s p i + marginalMeanEntropy s p i - Companion.Analytic.entropy (finalDensity s p)

/-- Planned lemma holevo_dimension: the original final system has dimension d. -/
def HolevoDimension : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d), 0<d →
    Companion.Analytic.entropy (finalDensity s p)-recordMeanEntropy s p ≤ Real.logb 2 d

/-- Planned lemma quantum_conditional_subadditivity, for the correlated record. -/
def QuantumConditionalSubadditivity : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d),
    recordEntropy s p + recordMeanEntropy s p - Companion.Analytic.entropy (finalDensity s p) ≤
      ∑ i : Fin m, marginalConditionalEntropy s p i

/-- Planned lemma quantum_fano: decoder acts on d, including mixed branches. -/
def QuantumFano : Prop :=
  ∀ (d m : ℕ) (s : State d) (p : Fin m → Measurement d) (i : Fin m) (e : ℝ),
    0≤e → e≤1/2 → decodeFailure s p i≤e →
    marginalConditionalEntropy s p i≤binaryEntropy e+e

end
end E2.Turn9
