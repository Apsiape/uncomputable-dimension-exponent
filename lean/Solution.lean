import Statement
import E2.Effective
import E2.GameConsequences

namespace E2

theorem challenge (hT : RealArithmetic.TarskiDecision) : MainStatement := by
  obtain ⟨hvalue,hperfect,hexponent⟩ := contextGame_conclusions
  exact ⟨contextGame,hvalue,hperfect,hexponent,exponent_halting_degree,
    no_certified_rate hT contextGame hvalue⟩

end E2
