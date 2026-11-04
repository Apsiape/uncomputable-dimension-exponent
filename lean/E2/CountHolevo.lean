import E2.CountNormalization
import E2.Turn9.CountInformationStatements

namespace E2
noncomputable section
open Turn9 Companion.Analytic
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

 theorem psd_sum {ι : Type*} [Fintype ι] {d : ℕ} (A : ι → Mat d)
    (hA : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef := by
  classical
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero (fun i _ => hA i)

 theorem psd_eigenvalue_sum {d : ℕ} (A : Mat d) (hA : A.PosSemidef) :
    (∑ i, hA.isHermitian.eigenvalues i)=A.trace.re := by
  have h := congrArg Complex.re hA.isHermitian.trace_eq_sum_eigenvalues
  simpa using h.symm

 theorem psd_entropy_nonneg {d : ℕ} (A : Mat d) (hA : A.PosSemidef)
    (htrace : A.trace.re≤1) : 0≤entropy A := by
  rw [entropy, dite_eq_left hA.isHermitian]
  apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  apply Finset.sum_nonneg
  intro i hi
  apply Real.negMulLog_nonneg (hA.eigenvalues_nonneg i)
  calc
    _ ≤ ∑ j, hA.isHermitian.eigenvalues j :=
      Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) hi
    _ ≤ 1 := by rw [psd_eigenvalue_sum A hA]; exact htrace

 theorem probability_entropy_dimension {d : ℕ} (hd : 0<d) (w : Fin d → ℝ)
    (hw : ∀ i, 0≤w i) (hn : (∑ i, w i)=1) :
    (∑ i, Real.negMulLog (w i)) ≤ Real.log d := by
  have hdim : (0:ℝ)<d := by exact_mod_cast hd
  have hpoint (i : Fin d) : (d:ℝ)*Real.negMulLog (w i) ≤
      1-(d:ℝ)*w i+w i*((d:ℝ)*Real.log d) := by
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hdim.le (hw i))
    rw [Real.negMulLog_mul] at h
    simp only [Real.negMulLog] at h ⊢
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [←Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ←Finset.sum_mul, hn] at hsum
  nlinarith

 theorem psd_entropy_dimension {d : ℕ} (hd : 0<d) (A : Mat d) (hA : A.PosSemidef)
    (htrace : A.trace.re=1) : entropy A ≤ Real.logb 2 d := by
  rw [entropy, dite_eq_left hA.isHermitian, Real.logb]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
  exact probability_entropy_dimension hd _ (hA.eigenvalues_nonneg)
    ((psd_eigenvalue_sum A hA).trans htrace)

 theorem record_density_positive {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) :
    (recordDensity s p a).PosSemidef := s.positive.mul_mul_conjTranspose_same _

 theorem record_density_mass {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) :
    (recordDensity s p a).trace.re=recordMass s p a := by
  unfold recordMass recordDensity
  rw [hs_square_gram, s.xi_positive.isHermitian.eq]
  congr 1
  calc
    _ = (reverseWord p a*(s.xi*s.xi)*(reverseWord p a).conjTranspose).trace := by rw [s.xi_square]
    _ = ((reverseWord p a*s.xi)*(s.xi*(reverseWord p a).conjTranspose)).trace := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
 theorem normalized_record_positive {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) :
    (normalizedDensity s (recordMass s p a) (recordDensity s p a)).PosSemidef := by
  unfold normalizedDensity
  split_ifs with h
  · exact s.positive
  · have hmass : 0≤(recordMass s p a)⁻¹ := inv_nonneg.mpr ((record_normalization d m s p).1 a)
    have h := (record_density_positive s p a).smul hmass
    convert h using 1

 theorem normalized_record_trace {d m : ℕ} (s : State d) (p : Fin m → Measurement d) (a : RecordType p) :
    (normalizedDensity s (recordMass s p a) (recordDensity s p a)).trace.re=1 := by
  unfold normalizedDensity
  split_ifs with h
  · rw [s.normalized]; norm_num
  · rw [Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      record_density_mass, inv_mul_cancel₀ h]

 theorem final_density_positive {d m : ℕ} (s : State d) (p : Fin m → Measurement d) :
    (finalDensity s p).PosSemidef := psd_sum _ (record_density_positive s p)

 theorem final_density_trace {d m : ℕ} (s : State d) (p : Fin m → Measurement d) :
    (finalDensity s p).trace.re=1 := by
  simp only [finalDensity, Matrix.trace_sum, Complex.re_sum, record_density_mass]
  exact (record_normalization d m s p).2

 theorem holevo_dimension : Turn9.HolevoDimension := by
  intro d m s p hd
  have hmean : 0≤recordMeanEntropy s p := Finset.sum_nonneg (fun a _ => mul_nonneg
    ((record_normalization d m s p).1 a)
    (psd_entropy_nonneg _ (normalized_record_positive s p a) (normalized_record_trace s p a).le))
  have hdim := psd_entropy_dimension hd _ (final_density_positive s p) (final_density_trace s p)
  linarith

end
end E2


