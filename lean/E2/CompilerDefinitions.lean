import E2.Source

namespace E2
noncomputable section
open Poly

def assignmentPolynomial (G : BCSGame) (c : Fin G.contexts)
    (a : Fin G.numVars → Bool) : Poly (Fin G.numVars) :=
  ((G.scope c).toList.map (fun v =>
    .const (1/2) * (1 + (if a v then 1 else -1) * .var v))).foldr (· * ·) 1

/-- Ordinary Boolean contexts impose commutation and the vanishing of each
forbidden joint-assignment projection. No parity-only restriction is made. -/
def booleanPresentation (G : BCSGame) : Presentation (Fin G.numVars) :=
  ⟨fun _ => .reflection,
   (List.finRange G.contexts).flatMap (fun c =>
     commList ((G.scope c).toList.map Poly.var) ((G.scope c).toList.map Poly.var) ++
     ((Finset.univ \ G.allowed c).toList.map (assignmentPolynomial G c)))⟩

structure CompiledPresentation {ι : Type*} (P : Presentation ι) where
  game : BCSGame
  dimensionFactor : ℕ
  factor_pos : 0 < dimensionFactor
  errorFactor : ℝ
  error_pos : 0 < errorFactor
  soundness : ∀ (η : ℝ) (d : ℕ) (m : Model (booleanPresentation game) d η), 0 ≤ η →
    ∃ out : Model P d (errorFactor*η), out.state = m.state
  completeness : ∀ (δ : ℝ) (d : ℕ) (m : Model P d δ), 0 ≤ δ → m.Flat →
    ∃ d', 0 < d' ∧ d' ≤ dimensionFactor*d ∧
      ∃ s : Strategy game d', loss s ≤ errorFactor*δ^2

end
end E2
