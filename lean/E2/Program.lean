import E2.RecognizerImplementation

namespace E2

/-- Section 5: the counter-machine implementation of Mathlib's universal
partial-recursive evaluator. The paper gives an algorithm, not an instruction
table; compiling that algorithm is an explicit outstanding proof obligation. -/
theorem recognizer_exists : ∃ p : CounterProgram, RecognizesK p := by
  exact RecognizerImplementation.exists_correct

noncomputable def recognizer : CounterProgram := Classical.choose recognizer_exists
theorem recognizer_correct : RecognizesK recognizer := Classical.choose_spec recognizer_exists

end E2
