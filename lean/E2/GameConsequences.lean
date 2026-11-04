import E2.Transfer

namespace E2

/-- The analytic conclusions for the original compiled ordinary Boolean game. -/
theorem contextGame_conclusions : quantumValue contextGame = 1 ∧
    NoPerfectStrategy contextGame ∧ DimensionExponent contextGame betaK :=
  game_exponent_of_profiles PK contextGame game_transfers matched_source_profiles
    (arbitrary_state_lower recognizer recognizer_correct)

theorem contextGame_value_one : quantumValue contextGame = 1 := contextGame_conclusions.1

theorem contextGame_no_perfect : NoPerfectStrategy contextGame := contextGame_conclusions.2.1

theorem contextGame_dimension_exponent : DimensionExponent contextGame betaK := contextGame_conclusions.2.2

end E2
