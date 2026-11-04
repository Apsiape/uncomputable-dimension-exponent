import E2.FiniteClockMatrices
import E2.PolyEval

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

def clockValue (n : ℕ) : Fin 4 → Mat (2^(n+1)) :=
  ![finiteA (n+1),finiteP n,finiteT (n+1),finiteX n]

def clockSpec : Presentation (Fin 4) :=
  ⟨fun i => match i.val with
    | 0 => .positiveContraction | 1 => .projection | 2 => .unitary | _ => .reflection,
   clockRelations (.var 0) (.var 1) (.var 2) (.var 3)⟩

theorem clock_error (n : ℕ) : 3*(1/4:ℝ)^(n+1)=3*(4:ℝ)^(-((n+1:ℕ):ℤ)) := by
  simp only [zpow_neg,zpow_natCast,one_div,inv_pow]

theorem clock_domains (n : ℕ) (i : Fin 4) : (clockSpec.domain i).Holds (clockValue n i) := by
  fin_cases i
  · exact finiteA_domain (n+1)
  · exact finiteP_domain n
  · exact finiteT_domain (n+1)
  · exact finiteX_domain n

theorem clock_op_defects (n : ℕ) (r : Poly (Fin 4)) (hr : r ∈ clockSpec.relations) :
    ‖Poly.eval (clockValue n) r‖ ≤ 3*(4:ℝ)^(-((n+1:ℕ):ℤ)) := by
  simp only [clockSpec,clockRelations,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with h|h|h|h <;> subst r
  · have he : Poly.eval (clockValue n) (pc (.var 0) (.var 1))=0 := by
      simpa [Poly.eval,pc,clockValue] using finite_AP n
    rw [he,norm_zero]
    positivity
  · have he : Poly.eval (clockValue n)
        (conjP (.var 2) (.var 0)-(4*.var 0-3*.var 1))=
        finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose-
          ((4:ℂ) • finiteA (n+1)-(3:ℂ) • finiteP n) := by
      simp [Poly.eval,conjP,clockValue,Matrix.smul_mul,Matrix.mul_smul]
    rw [he,←clock_error]
    exact finite_affine_norm n
  · have he : Poly.eval (clockValue n)
        (.var 3*.var 1*.var 3-(1-.var 1))=0 := by
      simpa [Poly.eval,clockValue] using sub_eq_zero.mpr (finite_own_flip n)
    rw [he,norm_zero]
    positivity
  · have he : Poly.eval (clockValue n)
        (pc (.var 3) (conjP (.var 2) (.var 0)))=
        finiteX n*(finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose)-
          (finiteT (n+1)*finiteA (n+1)*(finiteT (n+1)).conjTranspose)*finiteX n := by
      simp [Poly.eval,pc,conjP,clockValue]
    rw [he,←clock_error]
    exact finite_tail_norm n

def clockModel (n : ℕ) : Model clockSpec (2^(n+1)) (3*(4:ℝ)^(-((n+1:ℕ):ℤ))) where
  positive_dimension := by positivity
  state := flatState (2^(n+1)) (by positivity)
  value := clockValue n
  domains := clock_domains n
  defects r hr := (weighted_le_norm _ _).trans (clock_op_defects n r hr)
  state_commutators i := by
    rw [flatState_commutes]
    have hz : hs (0:Mat (2^(n+1)))=0 := by simp [hs,hsNorm,hsSquared]
    rw [hz]
    positivity

theorem clockModel_flat (n : ℕ) : (clockModel n).Flat := by
  change (((2^(n+1):ℕ):ℂ)⁻¹) • 1=(1/((2^(n+1):ℕ):ℂ)) • 1
  rw [one_div]

end
end E2.FiniteConstruction
