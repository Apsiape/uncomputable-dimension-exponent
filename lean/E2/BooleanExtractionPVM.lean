import E2.BooleanExtraction
import E2.CompilerStrategy

namespace E2.BooleanExtraction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerStrategy E2.CompilerDomains Companion.Analytic
variable {G : BCSGame} {d : ℕ}

def contextValue (A : ContextPVM G d) (c : Fin G.contexts) (v : Fin G.numVars) : Mat d :=
  encodeProjection (A.marginal c v)

theorem marginal_value (A : ContextPVM G d) (c) (v) (a) :
    A.marginal c v * A.value c a = if a v then A.value c a else 0 := by
  classical
  simp only [ContextPVM.marginal, Finset.sum_mul, ite_mul, Matrix.zero_mul, A.multiply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [hba]
  · simp

def bitSign (b : Bool) : ℂ := if b then 1 else -1

theorem contextValue_eigen (A : ContextPVM G d) (c) (v) (a) :
    contextValue A c v * A.value c a = bitSign (a v) • A.value c a := by
  simp only [contextValue, encodeProjection, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.one_mul, marginal_value]
  cases a v <;> simp [bitSign] <;> module

theorem contextValue_commute (A : ContextPVM G d) (c) (v w) :
    contextValue A c v * contextValue A c w = contextValue A c w * contextValue A c v := by
  have he (v w) : contextValue A c v * contextValue A c w =
      ∑ a, (bitSign (a w) * bitSign (a v)) • A.value c a := by
    calc
      _ = (contextValue A c v * contextValue A c w) * (∑ a, A.value c a) := by
        rw [A.complete,Matrix.mul_one]
      _ = _ := by simp only [Finset.mul_sum,Matrix.mul_assoc,contextValue_eigen,
        Matrix.mul_smul,smul_smul]
  rw [he v w, he w v]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm]

theorem atom_eigen (A : ContextPVM G d) (c) (v) (a) (b : Bool) :
    Poly.eval (contextValue A c) (Poly.const (1/2) * (1 + (if b then 1 else -1) * .var v)) *
      A.value c a = if b = a v then A.value c a else 0 := by
  have he : Poly.eval (contextValue A c)
      (Poly.const (1/2) * (1 + (if b then 1 else -1) * .var v)) =
      (1/2:ℂ) • (1 + bitSign b • contextValue A c v) := by
    cases b <;> simp [Poly.eval,bitSign]
  rw [he]
  simp only [Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,contextValue_eigen,smul_smul]
  cases b <;> cases hb : a v <;> simp [hb,bitSign] <;> module

theorem eval_fold_product {ι : Type*} (x : ι → Mat d) (ps : List (Poly ι)) :
    Poly.eval x (ps.foldr (· * ·) 1) = (ps.map (Poly.eval x)).prod := by
  induction ps with
  | nil => exact Poly.eval_one x
  | cons p ps ih => exact congrArg (fun R => Poly.eval x p * R) ih

theorem list_eigen {ι : Type*} (f : ι → Mat d) (P : Mat d) (q : ι → Prop)
    [DecidablePred q] (hf : ∀ v, f v * P = if q v then P else 0) (vs : List ι) :
    (vs.map f).prod * P = if ∀ v ∈ vs, q v then P else 0 := by
  classical
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons,List.prod_cons,Matrix.mul_assoc,ih]
    by_cases ht : ∀ w ∈ vs, q w
    · rw [ite_eq_left ht,hf v]
      simp_all
    · rw [ite_eq_right ht,Matrix.mul_zero]
      simp_all

theorem assignment_eigen (A : ContextPVM G d) (c) (a b : Fin G.numVars → Bool)
    (vs : List (Fin G.numVars)) :
    Poly.eval (contextValue A c)
      ((vs.map (fun v => Poly.const (1/2) * (1 + (if b v then 1 else -1) * .var v))).foldr (· * ·) 1) *
      A.value c a = if ∀ v ∈ vs, b v = a v then A.value c a else 0 := by
  classical
  rw [eval_fold_product,List.map_map]
  have hh := list_eigen _ _ (fun v => b v = a v) (fun v => atom_eigen A c v a (b v)) vs
  by_cases h : ∀ v ∈ vs, b v = a v
  · simpa only [Function.comp_def,ite_eq_left h] using hh
  · simpa only [Function.comp_def,ite_eq_right h] using hh

theorem contextValue_forbidden (A : ContextPVM G d) (c)
    (b : Fin G.numVars → Bool) (hb : b ∉ G.allowed c) :
    Poly.eval (contextValue A c) (assignmentPolynomial G c b) = 0 := by
  classical
  have hzero a : Poly.eval (contextValue A c) (assignmentPolynomial G c b) * A.value c a = 0 := by
    have he : Poly.eval (contextValue A c) (assignmentPolynomial G c b) * A.value c a =
        if ∀ v ∈ G.scope c, b v = a v then A.value c a else 0 := by
      simpa only [assignmentPolynomial,Finset.mem_toList] using assignment_eigen A c a b (G.scope c).toList
    rw [he]
    split_ifs with hm
    · apply A.legal c a
      intro ha
      exact hb ((G.locality c b a hm).mpr ha)
    · rfl
  calc
    _ = Poly.eval (contextValue A c) (assignmentPolynomial G c b) * (∑ a, A.value c a) := by
      rw [A.complete,Matrix.mul_one]
    _ = 0 := by simp only [Finset.mul_sum,hzero,Finset.sum_const_zero]

def ContextRepresentation.ofPVM (A : ContextPVM G d) : ContextRepresentation G d where
  value := contextValue A
  domains c v := encode_projection _ (A.marginal_projection c v)
  commutes c v hv w hw := contextValue_commute A c v w
  forbidden := contextValue_forbidden A

/-- The original-label legal PVM stage discharges every model field from its
incidence consistency estimate, with the original state and Bob dimension. -/
theorem model_of_pvm_consistency {a : ℕ}
    (ha : 0 < a) (s : State d) (Xi : Matrix (Fin d) (Fin a) ℂ)
    (hρ : s.rho = Xi * Xi.conjTranspose) (B : Fin G.numVars → Mat d)
    (hB : ∀ v, Domain.reflection.Holds (B v)) (A : ContextPVM G a)
    (η : ℝ) (hη : 0 ≤ η)
    (hc : ∀ c v, v ∈ G.scope c → hs (B v * Xi - Xi * contextValue A c v) ≤ η)
    (hu : ∀ v, (∀ c, v ∉ G.scope c) → B v = 1) :
    Nonempty (Model (booleanPresentation G) d (extractionConstant G * η)) :=
  model_of_context_consistency ha s Xi hρ B hB (.ofPVM A) η hη hc hu

end
end E2.BooleanExtraction
