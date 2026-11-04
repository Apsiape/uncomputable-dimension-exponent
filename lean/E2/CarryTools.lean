import E2.MatrixFunctions
import E2.CantorCarryScalar
import E2.FunctionalCalculus
import E2.WeightedTransport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.Matrix.Order

namespace E2
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem state_dimension_pos {d : ℕ} (s : State d) : 0<d := by
  cases d with
  | zero => have h := s.normalized; simpa [Matrix.trace] using h
  | succ d => omega

theorem positive_contraction_norm {d : ℕ} {A : Mat d}
    (h : Domain.positiveContraction.Holds A) : ‖A‖≤1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg A h.1.nonneg).mpr
  exact sub_nonneg.mp h.2.nonneg

theorem unitary_adjoint {d : ℕ} {V : Mat d} (h : Domain.unitary.Holds V) :
    Domain.unitary.Holds V.conjTranspose := by
  exact ⟨by simpa using h.2,by simpa using h.1⟩

theorem unitary_power {d : ℕ} {V : Mat d} (h : Domain.unitary.Holds V) (i : ℕ) :
    Domain.unitary.Holds (V^i) := by
  let u : unitary (Mat d) := ⟨V,h⟩
  exact (u^i).property

theorem unitary_norm {d : ℕ} (hd : 0<d) {V : Mat d} (h : Domain.unitary.Holds V) : ‖V‖=1 := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  let u : unitary (Mat d) := ⟨V,h⟩
  exact CStarRing.norm_coe_unitary u

theorem unitary_conjugate_hermitian {d : ℕ} (V A : Mat d) (hA : A.IsHermitian) :
    (V*A*V.conjTranspose).IsHermitian := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    Matrix.isHermitian_conjTranspose_mul_mul V.conjTranspose hA

theorem matrix_function_conjugate {d : ℕ} (V A : Mat d) (hV : Domain.unitary.Holds V)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    V*matrixFunction f A*V.conjTranspose=matrixFunction f (V*A*V.conjTranspose) := by
  let u : unitary (Mat d) := ⟨V,hV⟩
  let φ := Unitary.conjStarAlgAut ℂ (Mat d) u
  have h := StarAlgHomClass.map_cfc (S:=ℂ) φ f A (finite_spectrum_continuous A f)
    (by change Continuous (fun x => V*x*V.conjTranspose); fun_prop)
    hA.isSelfAdjoint (unitary_conjugate_hermitian V A hA).isSelfAdjoint
  exact h

theorem unitary_conjugate_spectrum {d : ℕ} (V A : Mat d) (hV : Domain.unitary.Holds V) :
    spectrum ℝ (V*A*V.conjTranspose)=spectrum ℝ A := by
  let u : unitary (Mat d) := ⟨V,hV⟩
  let φ := Unitary.conjStarAlgAut ℂ (Mat d) u
  exact AlgEquiv.spectrum_eq (φ.toAlgEquiv.restrictScalars ℝ) A

theorem matrix_function_comp {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (g f : ℝ → ℝ) :
    matrixFunction g (matrixFunction f A)=matrixFunction (fun x => g (f x)) A := by
  exact (cfc_comp g f A hA.isSelfAdjoint
    (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop)
    (finite_spectrum_continuous A f)).symm

theorem real_smul_matrix {d : ℕ} (r : ℝ) (A : Mat d) : r • A=(r:ℂ) • A := by
  ext i j
  simp only [Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,smul_eq_mul]
  rfl

theorem matrix_function_const {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (r : ℝ) :
    matrixFunction (fun _ => r) A=(r:ℂ) • 1 := by
  rw [matrixFunction,cfc_const r A hA.isSelfAdjoint,Algebra.algebraMap_eq_smul_one,real_smul_matrix]

theorem matrix_function_add {d : ℕ} (A : Mat d) (g f : ℝ → ℝ) :
    matrixFunction g A+matrixFunction f A=matrixFunction (fun x => g x+f x) A :=
  (cfc_add A g f (finite_spectrum_continuous A g) (finite_spectrum_continuous A f)).symm

theorem matrix_function_real_smul {d : ℕ} (A : Mat d) (r : ℝ) (f : ℝ → ℝ) :
    (r:ℂ) • matrixFunction f A=matrixFunction (fun x => r*f x) A := by
  simpa only [matrixFunction,real_smul_matrix,smul_eq_mul] using
    (cfc_smul r f A (finite_spectrum_continuous A f)).symm

theorem matrix_function_spectrum {d : ℕ} {A : Mat d} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectrum ℝ (matrixFunction f A)=f '' spectrum ℝ A :=
  cfc_map_spectrum f A hA.isSelfAdjoint (finite_spectrum_continuous A f)

theorem matrix_function_norm_bound {d : ℕ} (A : Mat d) (f : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (hf : ∀ x∈spectrum ℝ A,|f x|≤B) : ‖matrixFunction f A‖≤B := by
  apply norm_cfc_le hB
  simpa only [Real.norm_eq_abs] using hf

theorem cantor_mem_bounds {a : ℝ} (ha : a∈cantorSet) : 0≤a ∧ a≤1 := by
  obtain ⟨b,rfl⟩ := ha
  exact cantorCoordinate_bounds b

theorem cantor_translation_mem (i : ℕ) {a : ℝ} (ha : a∈cantorSet) : cantorTranslation i a∈cantorSet := by
  obtain ⟨b,rfl⟩ := ha
  exact ⟨addBits i b,(cantorTranslation_on_bits i b).symm⟩

theorem cantor_translation_zero {a : ℝ} (ha : a∈cantorSet) : cantorTranslation 0 a=a := by
  obtain ⟨b,rfl⟩ := ha
  rw [cantorTranslation_on_bits,addBits_zero]

theorem cantor_carry_bounds {a : ℝ} (ha : a∈cantorSet) : 0≤carryFunction a ∧ carryFunction a≤1 := by
  obtain ⟨b,rfl⟩ := ha
  rw [carryFunction_on_bits]
  exact carryOnBits_bounds b

theorem cantor_tail_mem {a : ℝ} (ha : a∈cantorSet) : tailFunction a∈cantorSet := by
  obtain ⟨b,rfl⟩ := ha
  exact ⟨dropBits b 1,(tailFunction_on_bits b).symm⟩

theorem digitFunction_lipschitz : LipschitzWith 2 digitFunction := by
  apply LipschitzWith.of_le_add_mul 2
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  unfold digitFunction
  split_ifs <;> by_cases hxy : 0≤x-y
  all_goals first | (rw [abs_of_nonneg hxy]; linarith) | (rw [abs_of_neg (lt_of_not_ge hxy)]; linarith)

theorem tailFunction_lipschitz : LipschitzWith 4 tailFunction := by
  apply LipschitzWith.of_le_add_mul 4
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  unfold tailFunction digitFunction
  split_ifs <;> by_cases hxy : 0≤x-y
  all_goals first | (rw [abs_of_nonneg hxy]; linarith) | (rw [abs_of_neg (lt_of_not_ge hxy)]; linarith)

theorem digitAt_lipschitz (j : ℕ) : LipschitzWith (2*4^j) (digitAt j) :=
  digitFunction_lipschitz.comp (tailFunction_lipschitz.iterate j)

theorem tail_iterate_on_bits (j : ℕ) (b : ℕ → Bool) :
    tailFunction^[j] (cantorCoordinate b)=cantorCoordinate (dropBits b j) := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply,tailFunction_on_bits,ih]
    congr 1

theorem digitAt_on_bits (j : ℕ) (b : ℕ → Bool) :
    digitAt j (cantorCoordinate b)=if b j then 1 else 0 := by
  rw [digitAt,tail_iterate_on_bits,digitFunction_on_bits]
  simp only [dropBits,Nat.zero_add]

theorem cantor_digit_bounds (j : ℕ) {a : ℝ} (ha : a∈cantorSet) :
    0≤digitAt j a ∧ digitAt j a≤1 := by
  obtain ⟨b,rfl⟩ := ha
  rw [digitAt_on_bits]
  split <;> norm_num

theorem cantor_matrix_norm {d : ℕ} {A : Mat d} (hA : HasCantorSpectrum A) : ‖A‖≤1 := by
  rw [← matrix_function_id hA.1]
  apply matrix_function_norm_bound _ _ 1 (by norm_num)
  intro x hx
  change |x|≤1
  exact abs_le.mpr ⟨by linarith [(cantor_mem_bounds (hA.2 hx)).1],(cantor_mem_bounds (hA.2 hx)).2⟩

theorem cantor_function_norm {d : ℕ} {A : Mat d} (hA : HasCantorSpectrum A)
    (f : ℝ → ℝ) (hf : ∀ x∈cantorSet,0≤f x ∧ f x≤1) : ‖matrixFunction f A‖≤1 := by
  apply matrix_function_norm_bound _ _ 1 (by norm_num)
  intro x hx
  exact abs_le.mpr ⟨by linarith [(hf x (hA.2 hx)).1],(hf x (hA.2 hx)).2⟩

theorem unitary_adjoint_state_commutator {d : ℕ} (s : State d) (V : Mat d)
    (hV : Domain.unitary.Holds V) : hs (comm V.conjTranspose s.xi)=hs (comm V s.xi) := by
  have he : comm V.conjTranspose s.xi= -(V.conjTranspose*comm V s.xi*V.conjTranspose) := by
    calc
      _ = -(V.conjTranspose*V*s.xi*V.conjTranspose-V.conjTranspose*s.xi*(V*V.conjTranspose)) := by
        rw [hV.1,hV.2]
        simp only [Matrix.one_mul,Matrix.mul_one,comm,Companion.Analytic.comm]
        abel
      _ = _ := by simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_assoc]
  rw [he,hs_neg_matrix]
  exact hs_biunitary V V.conjTranspose hV (unitary_adjoint hV) _

theorem weighted_sub_symm {d : ℕ} (s : State d) (A B : Mat d) : weighted s (A-B)=weighted s (B-A) := by
  have he : (A-B)*s.xi= -((B-A)*s.xi) := by simp only [Matrix.sub_mul]; abel
  unfold weighted
  rw [he,hs_neg_matrix]

theorem weighted_nonneg {d : ℕ} (s : State d) (A : Mat d) : 0≤weighted s A :=
  hsNorm_nonneg _

theorem weighted_neg {d : ℕ} (s : State d) (A : Mat d) : weighted s (-A)=weighted s A := by
  simp only [weighted,Matrix.neg_mul,hs_neg_matrix]

theorem weighted_sub_le {d : ℕ} (s : State d) (A B : Mat d) :
    weighted s (A-B)≤weighted s A+weighted s B := by
  simpa only [sub_eq_add_neg,weighted_neg] using weighted_add s A (-B)

theorem weighted_real_smul {d : ℕ} (s : State d) (r : ℝ) (A : Mat d) (hr : 0≤r) :
    weighted s ((r:ℂ) • A)=r*weighted s A := by
  unfold weighted hs hsNorm hsSquared
  simp only [Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,Complex.normSq_mul,
    Complex.normSq_ofReal,← Finset.mul_sum]
  rw [← pow_two,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr]

theorem weighted_smul {d : ℕ} (s : State d) (z : ℂ) (A : Mat d) :
    weighted s (z • A)=‖z‖*weighted s A := by
  unfold weighted hs hsNorm hsSquared
  simp only [Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,Complex.normSq_mul,
    Complex.normSq_eq_norm_sq,norm_mul,mul_pow,← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg ‖z‖),Real.sqrt_sq (norm_nonneg z)]

@[simp] theorem digitAt_zero : digitAt 0=digitFunction := rfl

theorem matrix_function_tail {d : ℕ} {A : Mat d} (hA : A.IsHermitian) :
    matrixFunction tailFunction A=(4:ℂ) • A-(3:ℂ) • matrixFunction digitFunction A := by
  calc
    _ = matrixFunction (fun x => 4*x) A-matrixFunction (fun x => 3*digitFunction x) A :=
      (matrix_function_sub A _ _).symm
    _ = _ := by
      have h4 : matrixFunction (fun x => 4*x) A=(4:ℂ) • A := by
        simpa [matrix_function_id hA] using (matrix_function_real_smul A 4 id).symm
      have h3 : matrixFunction (fun x => 3*digitFunction x) A=(3:ℂ) • matrixFunction digitFunction A := by
        simpa using (matrix_function_real_smul A 3 digitFunction).symm
      rw [h4,h3]

theorem matrix_function_carry_recursion {d : ℕ} {A : Mat d} (hA : HasCantorSpectrum A) :
    matrixFunction carryFunction A=1-matrixFunction digitFunction A+
      (1/4:ℂ) • (matrixFunction digitFunction A*matrixFunction carryFunction (matrixFunction tailFunction A)) := by
  rw [matrix_function_comp hA.1, matrix_function_mul]
  have hr : (1/4:ℂ) • matrixFunction (fun x => digitFunction x*carryFunction (tailFunction x)) A=
      matrixFunction (fun x => (1/4)* (digitFunction x*carryFunction (tailFunction x))) A := by
    simpa using matrix_function_real_smul A (1/4) (fun x => digitFunction x*carryFunction (tailFunction x))
  rw [hr]
  have hc : (1 : Mat d)=matrixFunction (fun _ => (1:ℝ)) A := by
    simpa using (matrix_function_const hA.1 1).symm
  rw [hc]
  rw [matrix_function_sub,matrix_function_add]
  apply matrix_function_congr hA.1
  intro x hx
  convert carryFunction_recursion x (hA.2 hx) using 1 <;> ring

theorem matrix_function_carry_step {d : ℕ} {A : Mat d} (hA : HasCantorSpectrum A) :
    matrixFunction (cantorTranslation 1) A=A-1+(7/4:ℂ) • matrixFunction carryFunction A := by
  conv_rhs => lhs; lhs; rw [← matrix_function_id hA.1]
  have hc : (1 : Mat d)=matrixFunction (fun _ => (1:ℝ)) A := by
    simpa using (matrix_function_const hA.1 1).symm
  have hr : (7/4:ℂ) • matrixFunction carryFunction A=matrixFunction (fun x => (7/4)*carryFunction x) A := by
    simpa using matrix_function_real_smul A (7/4) carryFunction
  rw [hc,matrix_function_sub,hr,matrix_function_add]
  exact matrix_function_congr hA.1 _ _ (fun x hx => cantorTranslation_one x (hA.2 hx))

theorem matrix_function_translate_comp {d : ℕ} {A : Mat d} (hA : HasCantorSpectrum A) (i j : ℕ) :
    matrixFunction (cantorTranslation i) (matrixFunction (cantorTranslation j) A)=
      matrixFunction (cantorTranslation (i+j)) A := by
  rw [matrix_function_comp hA.1]
  exact matrix_function_congr hA.1 _ _ (fun x hx => (cantorTranslation_composition i j x (hA.2 hx)).symm)

theorem unitary_power_state {d : ℕ} (s : State d) (V : Mat d) (hV : Domain.unitary.Holds V)
    (δ : ℝ) (hδ : 0≤δ) (hstate : hs (comm V s.xi)≤δ) (i : ℕ) :
    hs (comm (V^i) s.xi)≤(i:ℝ)*δ := by
  simpa only [List.prod_replicate,List.length_replicate] using
    word_state_commutator s (state_dimension_pos s) δ hδ (List.replicate i V)
      (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact (unitary_norm (state_dimension_pos s) hV).le)
      (by intro a ha; rw [(List.mem_replicate.mp ha).2]; exact hstate)

theorem translate_eq_conjugate {d : ℕ} (V A : Mat d) (i : ℕ) :
    translate V A i=V^i*A*(V^i).conjTranspose := by
  simp only [translate,Matrix.conjTranspose_pow]

theorem translate_succ {d : ℕ} (V A : Mat d) (i : ℕ) :
    translate V A (i+1)=V*translate V A i*V.conjTranspose := by
  simp only [translate,pow_succ',Matrix.mul_assoc]
  rw [← pow_succ',pow_succ]

theorem translate_norm {d : ℕ} (s : State d) (V A : Mat d) (hV : Domain.unitary.Holds V) (i : ℕ) :
    ‖translate V A i‖≤‖A‖ := by
  rw [translate_eq_conjugate]
  calc
    _ ≤ ‖V^i‖*‖A‖*‖(V^i).conjTranspose‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = _ := by rw [← Matrix.star_eq_conjTranspose,norm_star,unitary_norm (state_dimension_pos s) (unitary_power hV i)]; ring

theorem translate_weighted {d : ℕ} (s : State d) (V A : Mat d) (hV : Domain.unitary.Holds V)
    (δ : ℝ) (hδ : 0≤δ) (hstate : hs (comm V s.xi)≤δ) (i : ℕ) :
    weighted s (translate V A i)≤weighted s A+‖A‖*(i*δ) := by
  rw [translate_eq_conjugate]
  have ht := unitary_weighted_transport s (V^i).conjTranspose A (unitary_adjoint (unitary_power hV i))
  simp only [Matrix.conjTranspose_conjTranspose,unitary_adjoint_state_commutator s (V^i) (unitary_power hV i)] at ht
  exact ht.trans (add_le_add_right (mul_le_mul_of_nonneg_left (unitary_power_state s V hV δ hδ hstate i) (norm_nonneg A)) _)

end
end E2
