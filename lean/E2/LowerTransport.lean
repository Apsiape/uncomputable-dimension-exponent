import E2.JointAccounting

namespace E2
noncomputable section
open Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

 theorem state_hs_xi {d : ℕ} (s : State d) : hs s.xi = 1 := by
  have h : hs s.xi ^ 2 = 1 := by
    rw [hsNorm_sq, hsSquared_trace, s.xi_positive.isHermitian.eq, s.xi_square, s.normalized]
    norm_num
  nlinarith [hsNorm_nonneg s.xi]

 theorem projection_expectation_eq {d : ℕ} (s : State d) (F : Mat d)
    (hF : Domain.projection.Holds F) : expectation s F = hs (F*s.xi)^2 := by
  rw [hs_square_gram, hF.1, hF.2, s.xi_positive.isHermitian.eq]
  unfold expectation
  congr 1
  rw [Matrix.trace_mul_cycle, s.xi_square]

 theorem projection_weighted_le_one {d : ℕ} (s : State d) (F : Mat d)
    (hF : Domain.projection.Holds F) : hs (F*s.xi) ≤ 1 := by
  calc
    _ ≤ ‖F‖ * hs s.xi := operator_mul_hs F s.xi
    _ ≤ 1 := by rw [state_hs_xi, mul_one]; exact projection_norm_le hF

/-- Squared norm variation for two subnormalized amplitudes. -/
 theorem hs_square_variation {d : ℕ} (A B : Mat d) (hA : hs A ≤ 1) (hB : hs B ≤ 1) :
    |hs A^2-hs B^2| ≤ 2*hs (A-B) := by
  have ha := hsNorm_nonneg A
  have hb := hsNorm_nonneg B
  have hd := hsNorm_nonneg (A-B)
  have h1 : hs A ≤ hs (A-B)+hs B := by
    have h := hsNorm_add_le (A-B) B
    simpa only [sub_add_cancel] using h
  have h2 : hs B ≤ hs (A-B)+hs A := by
    have h := hsNorm_add_le (-(A-B)) A
    have he : -(A-B)+A=B := by abel
    change hs (-(A-B)+A) ≤ hs (-(A-B))+hs A at h
    rw [he,hs_neg_matrix] at h
    exact h
  have hab : |hs A-hs B| ≤ hs (A-B) := abs_le.mpr ⟨by linarith,by linarith⟩
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg ha hb)]
  exact mul_le_mul (by linarith : hs A+hs B≤2) hab (abs_nonneg _) (by norm_num)

/-- Unitary flag transport on an arbitrary original mixed state; no trace-flatness. -/
 theorem flag_translate_expectation {d : ℕ} (s : State d) (V F : Mat d) (δ : ℝ)
    (hV : Domain.unitary.Holds V) (hF : Domain.projection.Holds F)
    (hstate : hs (comm V s.xi) ≤ δ) (i : ℕ) :
    |expectation s (translate V F i)-expectation s F| ≤ 2*i*δ := by
  have hδ : 0 ≤ δ := (hsNorm_nonneg _).trans hstate
  let W := V^i
  have hW : Domain.unitary.Holds W := unitary_power hV i
  let A := F*W.conjTranspose*s.xi
  let B := F*s.xi*W.conjTranspose
  have htrans : hs (translate V F i*s.xi)=hs A := by
    rw [translate_eq_conjugate]
    change hs (W*F*W.conjTranspose*s.xi)=_
    have h := hsNorm_unitary_left W A hW.1
    simpa only [A,Matrix.mul_assoc] using h
  have hbase : hs B=hs (F*s.xi) := hsNorm_unitary_right W.conjTranspose _ (by simpa using hW.1)
  have hA : hs A ≤ 1 := by
    rw [←htrans]
    exact projection_weighted_le_one s _ (translate_projection V F hV hF i)
  have hB : hs B ≤ 1 := by rw [hbase]; exact projection_weighted_le_one s F hF
  have hd : hs (A-B) ≤ (i:ℝ)*δ := by
    have he : A-B=F*comm W.conjTranspose s.xi := by
      dsimp [A,B]
      simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.mul_assoc]
    rw [he]
    calc
      _ ≤ ‖F‖*hs (comm W.conjTranspose s.xi) := operator_mul_hs _ _
      _ ≤ 1*((i:ℝ)*δ) := mul_le_mul (projection_norm_le hF)
        (by rw [unitary_adjoint_state_commutator s W hW]; exact unitary_power_state s V hV δ hδ hstate i)
        (hsNorm_nonneg _) (by positivity)
      _ = _ := one_mul _
  rw [projection_expectation_eq s _ (translate_projection V F hV hF i),
    projection_expectation_eq s F hF,htrans,←hbase]
  exact (hs_square_variation A B hA hB).trans (by linarith)

 theorem source_flag_transport {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (i : ℕ) :
    |expectation m.state (translate (modelValue m 12) (modelValue m 18) i) -
      expectation m.state (modelValue m 18)| ≤ 2*i*δ := by
  apply flag_translate_expectation
  · simpa [sourceDomain,modelValue,sourceAt] using sourceAt_domain m 12 (by omega)
  · simpa [sourceDomain,modelValue,sourceAt] using sourceAt_domain m 18 (by omega)
  · exact sourceAt_state m 12

/-- Uniform lower estimate for the entire optional block, on its original state. -/
 theorem joint_active_lower {p : CounterProgram} {d M : ℕ} {δ K : ℝ}
    (m : Model (sourcePresentation p) d δ) (r : JointFamily m M K) (hδ : 0 ≤ δ) :
    (M:ℝ)*expectation m.state (modelValue m 18) - 2*(M:ℝ)^2*δ ≤ activeSum m.state r.measurement := by
  rw [r.active_sum]
  have h (i : Fin M) : expectation m.state (modelValue m 18) - 2*(M:ℝ)*δ ≤
      expectation m.state (translate (modelValue m 12) (modelValue m 18) i.val) := by
    have hi := (abs_le.mp (source_flag_transport m i.val)).1
    have him : (i.val:ℝ) ≤ M := by exact_mod_cast i.isLt.le
    have hmul := mul_le_mul_of_nonneg_right him hδ
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  convert hs using 1 <;> simp [Finset.sum_const] <;> ring
/-
    (show (M:ℝ)*(expectation m.state (modelValue m 18)-2*M*δ) ≤ _ from hs) -/

end
end E2


