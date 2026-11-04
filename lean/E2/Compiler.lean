import E2.CompilerUpperCompleteness
import E2.CompilerSoundnessRealize

namespace E2
noncomputable section
open Poly

/-- Theorem 3.1, all quantifiers, exact same-space/same-state soundness and
flat quadratic-loss completeness. Source guards remain polynomial factors. -/
theorem polynomial_compiler {ι : Type*} [Fintype ι] (P : Presentation ι) :
    Nonempty (CompiledPresentation P) := by
  obtain ⟨Cs,hCs,hs⟩ := CompilerNetwork.realize_soundness P
  obtain ⟨Cc,hCc,hc⟩ := CompilerUpper.realize_completeness P
  refine ⟨{
    game := CompilerNetwork.realize P
    dimensionFactor := CompilerUpper.wireDimensionFactor P
    factor_pos := CompilerUpper.wireDimensionFactor_pos P
    errorFactor := Cs+Cc
    error_pos := add_pos hCs hCc
    soundness := ?_
    completeness := ?_ }⟩
  · intro η d m hη
    obtain ⟨out,hstate⟩ := hs η d m hη
    refine ⟨out.weaken ?_,hstate⟩
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCc.le) hη
  · intro δ d m hδ hm
    obtain ⟨d',hd',hfactor,S,hS⟩ := hc δ d m hδ hm
    refine ⟨d',hd',hfactor,S,hS.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCs.le) (sq_nonneg δ)

/-- The own-variable AND context for E is an ordinary Boolean predicate.
`e` is distinct from the X variables. This is used before orthogonality repair. -/
def selectorAndPredicate (q : ℕ) (a : Fin (q+1) → Bool) : Prop :=
  a ⟨q, Nat.lt_succ_self q⟩ = true ↔ ∀ i : Fin q, a i.castSucc = true

/-- The orthogonality context contains precisely x_E and x_F. -/
def selectorOrthogonalityPredicate (a : Fin 2 → Bool) : Prop :=
  ¬ (a 0 = true ∧ a 1 = true)

def compiledSource : CompiledPresentation PK := Classical.choice (polynomial_compiler PK)
def contextGame : BCSGame := compiledSource.game

end
end E2
