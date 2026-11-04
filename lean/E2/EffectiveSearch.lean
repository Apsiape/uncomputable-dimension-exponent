import E2.EffectiveCoding
import E2.PositivePrecision

namespace E2.EffectiveSearch
noncomputable section
open EffectiveCoding

theorem fixed_precision_of_decision (G : BCSGame) (hG : quantumValue G = 1)
    (hF : ComputablePred (fun nd : ℕ × ℕ => Feasible G (rationalCode nd.1) nd.2)) :
    Computable (fun n : ℕ => if 0 < rationalCode n then
      (dimension G (rationalCode n)).toNat else 0) := by
  classical
  let P : ℕ → ℕ → Prop := fun n d => if 0 < rationalCode n then
    Feasible G (rationalCode n) d else d = 0
  have hpos : Computable (fun nd : ℕ × ℕ => decide (0 < rationalCode nd.1)) :=
    rat_lt.decide.to_comp.comp (Computable.const 0)
      (rational_decode.to_comp.comp Computable.fst)
  have hp : ComputablePred (fun nd : ℕ × ℕ => P nd.1 nd.2) := by
    apply Computable.computablePred
    refine (hpos.cond hF.decide
      (Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const 0))).of_eq ?_
    intro nd
    by_cases h : 0 < rationalCode nd.1 <;> simp [P,h]
  have hex : ∀ n, ∃ d, P n d := by
    intro n
    by_cases h : 0 < rationalCode n
    · simpa [P,h] using positive_precision_feasible G hG (rationalCode n)
        ((Rat.cast_pos (K := ℝ)).mpr h)
    · exact ⟨0,by simp [P,h]⟩
  refine (Computable.find hp hex).of_eq ?_
  intro n
  by_cases h : 0 < rationalCode n
  · have hf := positive_precision_feasible G hG (rationalCode n)
      ((Rat.cast_pos (K := ℝ)).mpr h)
    simp only [h, ↓reduceIte, dimension, dif_pos hf, ENat.toNat_coe]
    apply le_antisymm
    · exact Nat.find_min' (hex n) (by simpa [P,h] using Nat.find_spec hf)
    · exact Nat.find_min' hf (by simpa [P,h] using Nat.find_spec (hex n))
  · simp only [h, ↓reduceIte]
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' (hex n) (by simp [P,h])

end
end E2.EffectiveSearch
