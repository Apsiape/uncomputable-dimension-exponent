import E2.EffectiveCoding

namespace E2.EffectiveOracle
noncomputable section
open Encodable EffectiveCoding

theorem query_reduction (x y : ℝ) (c : ℕ → ℕ) (hc : Computable c)
    (h : ∀ n, (rationalCode n : ℝ) < x ↔ (rationalCode (c n) : ℝ) < y) :
    TuringReducible (realOracle x) (realOracle y) := by
  have ho : Nat.RecursiveIn {realOracle y} (realOracle y) :=
    Nat.RecursiveIn.oracle _ (by simp)
  have hq : Nat.RecursiveIn {realOracle y} (fun n => Part.some (c n)) :=
    RecursiveIn.iff_nat.mp hc.computableIn
  apply RecursiveIn.iff_nat.mpr
  refine (ho.comp hq).of_eq ?_
  intro n
  have hb := Part.bind_some (c n) (fun m => realOracle y m)
  exact hb.trans (by simp only [realOracle, ← h n])

theorem affine_equivalent (x : ℝ) :
    TuringEquivalent (realOracle ((3+x)/4)) (realOracle x) := by
  have hforward : Computable (fun n => encode ((4:ℚ)*rationalCode n + (-3))) :=
    Computable.encode.comp
      (rat_add.comp (rat_mul.comp (Computable.const 4) rational_decode.to_comp)
        (Computable.const (-3)))
  have hback : Computable (fun n => encode ((rationalCode n + 3) * (1/4:ℚ))) :=
    Computable.encode.comp
      (rat_mul.comp (rat_add.comp rational_decode.to_comp (Computable.const 3))
        (Computable.const (1/4)))
  constructor
  · apply query_reduction _ _ _ hforward
    intro n
    rw [rational_encode]
    push_cast
    constructor <;> intro h <;> linarith
  · apply query_reduction _ _ _ hback
    intro n
    rw [rational_encode]
    push_cast
    constructor <;> intro h <;> linarith

end
end E2.EffectiveOracle
