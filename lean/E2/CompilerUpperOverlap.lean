import E2.CompilerUpperCorner
import E2.CompilerFlatUpperWires

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerTensor E2.CompilerBoolean
open E2.CompilerMultiSelector E2.FiniteConstruction Companion.Analytic
variable {ι : Type*} {d : ℕ} [Fintype ι]

/-- The exact forward and reverse products for successive conjugations. -/
theorem conjugateList_eq (L : List (Mat d)) (R : Mat d) :
    conjugateList L R = L.reverse.prod*R*L.prod := by
  induction L generalizing R with
  | nil => simp [conjugateList]
  | cons A L ih =>
    change conjugateList L (A*R*A)=_
    rw [ih]
    simp only [List.reverse_cons,List.prod_append,List.prod_singleton,List.prod_cons,List.prod_nil,mul_one,one_mul,mul_assoc]

theorem base_final_conjugacy (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) :
    baseConjugate P s r (steps P r)=baseWord P s r*baseE P r*
      (List.ofFn (baseControl P s r)).reverse.prod := by
  unfold baseConjugate
  rw [List.take_of_length_le (by simp),conjugateList_eq,ofFn_rev,List.reverse_reverse]
  rfl

theorem base_word_inverse (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ k, Domain.reflection.Holds (s k)) (r : Fin P.relations.length) :
    (List.ofFn (baseControl P s r)).reverse.prod*baseWord P s r=1 ∧
      baseWord P s r*(List.ofFn (baseControl P s r)).reverse.prod=1 := by
  have h : ∀ A ∈ List.ofFn (baseControl P s r), A*A=1 := by
    intro A hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
    exact (baseControl_domain P s hs r i).2
  exact ⟨reverse_involutions _ h,forward_involutions _ h⟩

theorem base_decoded_final (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ k, Domain.reflection.Holds (s k)) (r : Fin P.relations.length) :
    decodeProjection (baseConjugate P s r (steps P r))=
      baseWord P s r*decodeProjection (baseE P r)*
        (List.ofFn (baseControl P s r)).reverse.prod := by
  rw [base_final_conjugacy]
  simp only [decodeProjection,Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
  congr 1
  rw [mul_add,mul_one,add_mul,(base_word_inverse P s hs r).2]

/-- Flat right multiplication costs only the operator norm. -/
theorem flat_weighted_right (hd : 0<d) (A B : Mat d) :
    weighted (flatState d hd) (A*B) ≤ ‖B‖*weighted (flatState d hd) A := by
  have h := weighted_right (flatState d hd) B A
  rw [flatState_commutes,show hs (0:Mat d)=0 by simp [hs,hsNorm,hsSquared]] at h
  simpa only [mul_zero,add_zero] using h

theorem reflection_list_norm (hd : 0<d) (L : List (Mat d))
    (hL : ∀ A ∈ L, Domain.reflection.Holds A) : ‖L.prod‖≤1 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  induction L with
  | nil => simp
  | cons A L ih =>
    simp only [List.prod_cons]
    exact (norm_mul_le _ _).trans ((mul_le_mul
      (E2.CompilerFrontend.reflection_norm hd A (hL A (by simp)))
      (ih (fun B hB => hL B (by simp [hB]))) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

/-- Per-relation upper overlap estimate, deduced solely from the source defect. -/
theorem base_overlap_bound (P : Presentation ι) (δ : ℝ) (d : ℕ)
    (s : Model (E2.CompilerFrontend.reflectionPresentation P) d δ) (hs : s.Flat)
    (r : Fin P.relations.length) :
    weighted (flatState (registerSize P*d) (Nat.mul_pos (registerSize_pos P) s.positive_dimension))
      (decodeProjection (baseE P r)*decodeProjection (baseConjugate P s.value r (steps P r))) ≤
        ‖(normalization P r:ℂ)‖*δ := by
  let hd := Nat.mul_pos (registerSize_pos P) s.positive_dimension
  let st := flatState (registerSize P*d) hd
  let R := Poly.eval s.value
    (E2.CompilerFrontend.substitute (E2.CompilerFrontend.replacement P) (P.relations.get r))
  have hdef : weighted s.state R ≤ δ := s.defects _
    (List.mem_map.mpr ⟨P.relations.get r,List.get_mem _ _,rfl⟩)
  have he : ‖decodeProjection (baseE (d:=d) P r)‖≤1 :=
    projection_norm_le (decode_projection _ (baseE_domain P r))
  have hrev : ‖(List.ofFn (baseControl P s.value r)).reverse.prod‖≤1 := by
    apply reflection_list_norm hd
    intro A hA
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hA)
    exact baseControl_domain P s.value s.domains r i
  rw [base_decoded_final P s.value s.domains r]
  rw [← mul_assoc,← mul_assoc,base_normalized_corner P s.value s.domains r]
  calc
    _ ≤ weighted st (normalization P r •
        (E2.CompilerTensor.source (registerSize P) R*decodeProjection (baseE P r))) := by
      apply (flat_weighted_right hd _ _).trans
      exact (mul_le_mul_of_nonneg_right hrev (hsNorm_nonneg _)).trans_eq (one_mul _)
    _ = ‖(normalization P r:ℂ)‖*weighted st
        (E2.CompilerTensor.source (registerSize P) R*decodeProjection (baseE P r)) := by
      rw [rational_smul,E2.CompilerCertificates.weighted_smul]
    _ ≤ ‖(normalization P r:ℂ)‖*weighted st (E2.CompilerTensor.source (registerSize P) R) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (flat_weighted_right hd _ _).trans
      exact (mul_le_mul_of_nonneg_right he (hsNorm_nonneg _)).trans_eq (one_mul _)
    _ ≤ ‖(normalization P r:ℂ)‖*δ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [weighted_source (registerSize_pos P) s.positive_dimension,
        ← E2.CompilerFlat.flat_model_state s hs]
      exact hdef

/-- Step 3, with one strictly positive constant for all relations and dimensions. -/
theorem flat_base_overlap (P : Presentation ι) :
    ∃ C : ℝ, 0<C ∧ ∀ (δ : ℝ) (d : ℕ)
      (s : Model (E2.CompilerFrontend.reflectionPresentation P) d δ), 0≤δ → s.Flat →
      ∀ r : Fin P.relations.length,
      weighted (flatState (registerSize P*d) (Nat.mul_pos (registerSize_pos P) s.positive_dimension))
        (decodeProjection (baseE P r)*decodeProjection (baseConjugate P s.value r (steps P r))) ≤ C*δ := by
  classical
  let C : ℝ := 1+∑ r : Fin P.relations.length, ‖(normalization P r:ℂ)‖
  have hsum : 0≤∑ r : Fin P.relations.length, ‖(normalization P r:ℂ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro δ d s hδ hs r
  apply (base_overlap_bound P δ d s hs r).trans
  apply mul_le_mul_of_nonneg_right _ hδ
  have h := Finset.single_le_sum (fun r (_ : r ∈ Finset.univ) => norm_nonneg (normalization P r:ℂ))
    (Finset.mem_univ r)
  dsimp [C]
  linarith

end
end E2.CompilerUpper
