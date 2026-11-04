import E2.FeasibilityComputation
import E2.RationalLogarithm

namespace E2.EffectiveDyadic
noncomputable section
set_option maxHeartbeats 200000
open EffectiveCoding Primrec

def precision (n : ℕ) : ℚ := (1:ℚ)/(2^n : ℕ)

theorem precision_computable : Computable precision := by
  have hp : Primrec (fun n : ℕ => 2^n) := RationalLogarithm.nat_pow.comp (const 2) .id
  exact (rat_divNat.comp ((Computable.const 1).pair hp.to_comp)).of_eq (fun _ => rfl)

@[simp] theorem precision_cast (n : ℕ) : (precision n : ℝ) = (2:ℝ)^(-(n:ℤ)) := by
  simp [precision,zpow_neg,zpow_natCast,one_div]

theorem dimension_computable (hT : RealArithmetic.TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    Computable (fun n : ℕ => (dimension G ((2:ℝ)^(-(n:ℤ)))).toNat) := by
  have h := (FeasibilityComputation.fixed_precision hT G hG).comp
    (Computable.encode.comp precision_computable)
  refine h.of_eq ?_
  intro n
  have hp : 0 < precision n := by dsimp [precision]; positivity
  simp [rationalCode,Encodable.encodek,hp]

theorem dimension_positive (G : BCSGame) (hG : quantumValue G = 1) (n : ℕ) :
    0 < (dimension G ((2:ℝ)^(-(n:ℤ)))).toNat := by
  classical
  have h := positive_precision_feasible G hG ((2:ℝ)^(-(n:ℤ))) (by positivity)
  simp only [dimension,dite_eq_left h,ENat.toNat_natCast]
  exact (Nat.find_spec h).1

def approximation (m n k : ℕ) : ℚ := (Nat.log 2 (m^(2^(k+1))) : ℚ) / (2^(k+1)*n : ℕ)

theorem approximation_computable : Computable (fun p : ℕ × ℕ × ℕ => approximation p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : ℕ × ℕ × ℕ => 2^(p.2.2+1)) :=
    RationalLogarithm.nat_pow.comp (const 2) (succ.comp (snd.comp snd))
  have hj := RationalLogarithm.nat_log_two.comp (RationalLogarithm.nat_pow.comp fst ht)
  exact (rat_divNat.comp ((int_ofNat.comp hj).to_comp.pair
    (nat_mul.comp ht (fst.comp snd)).to_comp)).of_eq (fun _ => rfl)

theorem approximation_eq (m n k : ℕ) : approximation m n k = RationalLogarithm.approx m k / n := by
  simp [approximation,RationalLogarithm.approx,div_div,Nat.cast_mul]

theorem approximation_compose (D : ℕ → ℕ) (hD : Computable D) :
    Computable (fun p : ℕ × ℕ => approximation (D p.1) p.1 p.2) := by
  have hp : Computable (fun p : ℕ × ℕ => (D p.1,(p.1,p.2))) :=
    (hD.comp Computable.fst).pair (Computable.fst.pair Computable.snd)
  exact (approximation_computable.comp hp).of_eq (fun _ => rfl)

/-- Original dyadic slope, with its value zero at index zero. -/
theorem dyadic_sequence (hT : RealArithmetic.TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    ComputableRealSequence (dyadicSlope G) := by
  let D := fun n : ℕ => (dimension G ((2:ℝ)^(-(n:ℤ)))).toNat
  have hD : Computable D := dimension_computable hT G hG
  let q := fun p : ℕ × ℕ => approximation (D p.1) p.1 p.2
  have hq : Computable q := approximation_compose D hD
  refine ⟨fun p => Encodable.encode (q p),Computable.encode.comp hq,?_⟩
  intro n k
  simp only [rationalCode,Encodable.encodek,Option.getD_some]
  by_cases hn : n=0
  · subst n
    simp [q,approximation,dyadicSlope]
    positivity
  · have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have he := RationalLogarithm.approx_error (D n) k (dimension_positive G hG n)
    change |(approximation (D n) n k : ℝ)-Real.logb 2 (D n : ℝ)/(n:ℝ)| ≤ _
    rw [approximation_eq,Rat.cast_div,Rat.cast_natCast,← sub_div,abs_div,abs_of_pos hnpos]
    apply (div_le_iff₀ hnpos).mpr
    exact he.trans (le_mul_of_one_le_right (by positivity) hn1)

end
end E2.EffectiveDyadic

