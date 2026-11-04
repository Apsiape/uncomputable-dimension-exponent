import E2.CountConditional
import E2.CountFano
import E2.CountMove
import E2.CountEntropyLower

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators

theorem record_information_upper : Turn9.RecordInformationUpper := by
  intro d m s p e hd he0 hehalf herror
  have hdim := holevo_dimension d m s p hd
  have hsub := quantum_conditional_subadditivity d m s p
  have hf := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => quantum_fano d m s p i e he0 hehalf (herror i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hf
  linarith

theorem triangular_measurement_count_proof : ∃ C : ℝ, 0<C ∧
    ∀ (d m : ℕ) (s : State d) (η : ℝ) (p : Fin m → Measurement d) (u : Fin m → Mat d),
    0<d → 0≤η → TriangularRelations s η p u → C*m^4*η^2≤1/2 →
    Real.logb 2 d ≥ binaryCount p+activeSum s p-C*m^3*η-
      m*(binaryEntropy (C*m^4*η^2)+C*m^4*η^2) := by
  obtain ⟨CL,hCL,hlower⟩ := record_entropy_lower
  obtain ⟨CD,hCD,hdecode⟩ := decoder_error_bound
  refine ⟨CL+CD,add_pos hCL hCD,?_⟩
  intro d m s η p u hd hη hrel hsmall
  have hupper := record_information_upper d m s p ((CL+CD)*m^4*η^2) hd (by positivity) hsmall
    (fun i => (hdecode d m s η p hη hrel.2.1 hrel.2.2.1 i).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : CD≤CL+CD)
        (by positivity : (0:ℝ)≤m^4)) (sq_nonneg η)))
  have hlo := hlower d m s η p u hη hrel
  have hloss : CL*m^3*η ≤ (CL+CD)*m^3*η :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : CL≤CL+CD)
      (by positivity : (0:ℝ)≤m^3)) hη
  linarith

end
end E2
