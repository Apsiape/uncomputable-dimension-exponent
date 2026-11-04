import Solution
import E2.FunctionalCalculus
import E2.Effective
import E2.RawWords
import E2.ClockProfile
import E2.ClockExtras
import E2.Ideal

namespace E2

/-- Theorem 1.2 of v4.0.0 (label thm:main, eq. (1.4)) is Lean-checked, conditional on the explicit hypothesis TarskiDecision (Basu-Pollack-Roy, Theorem 13.13).
Audit.lean exposes the axioms of the assembled proof term. -/
theorem blueprint (hT : RealArithmetic.TarskiDecision) : MainStatement := by
  have h := game_exponent_of_profiles PK contextGame game_transfers
    matched_source_profiles (arbitrary_state_lower recognizer recognizer_correct)
  obtain ⟨hvalue,hperfect,hexponent⟩ := h
  exact ⟨contextGame,hvalue,hperfect,hexponent,exponent_halting_degree,
    no_certified_rate hT contextGame hvalue⟩

end E2
