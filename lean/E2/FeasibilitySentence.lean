import E2.RealArithmeticMatrix

namespace E2.FeasibilitySentence
noncomputable section
open scoped BigOperators ComplexOrder
open RealArithmetic

structure Data (G : BCSGame) (d : ℕ) (K : Type*) where
  rho : Matrix (Fin d × Fin d) (Fin d × Fin d) K
  alice : Fin G.contexts → (Fin G.numVars → Bool) → Matrix (Fin d) (Fin d) K
  bob : Fin G.numVars → Bool → Matrix (Fin d) (Fin d) K

def evaluate {G : BCSGame} {d : ℕ} (v : ℕ → ℝ) (X : Data G d CPoly) : Data G d ℂ where
  rho := evalMatrix v X.rho
  alice c a := evalMatrix v (X.alice c a)
  bob w b := evalMatrix v (X.bob w b)

def rawWinning {G : BCSGame} {d : ℕ} (X : Data G d ℂ) : ℝ :=
  ∑ c, ∑ w, (G.probability c w : ℝ) * ∑ a ∈ G.allowed c,
    (Matrix.trace (X.rho * Matrix.kronecker (X.alice c a) (X.bob w (a w)))).re

def winningPoly {G : BCSGame} {d : ℕ} (X : Data G d CPoly) : CPoly := by
  classical
  let E := enumProd (enumFin d) (enumFin d)
  exact total (enumFin G.contexts) fun c => total (enumFin G.numVars) fun w =>
    cmul (cconst (G.probability c w)) (csum ((G.allowed c).toList.map fun a =>
      total E fun i => total E fun j =>
        cmul (X.rho i j) (cmul (X.alice c a j.1 i.1) (X.bob w (a w) j.2 i.2))))

def lossPoly {G : BCSGame} {d : ℕ} (X : Data G d CPoly) : Poly :=
  sub (constant 1) (winningPoly X).1

@[simp] theorem winningPoly_eval {G : BCSGame} {d : ℕ} (v : ℕ → ℝ) (X : Data G d CPoly) :
    (ceval v (winningPoly X)).re = rawWinning (evaluate v X) := by
  classical
  simp [winningPoly,rawWinning,evaluate,evalMatrix,Matrix.trace,Matrix.mul_apply,
    Complex.mul_re]

@[simp] theorem lossPoly_eval {G : BCSGame} {d : ℕ} (v : ℕ → ℝ) (X : Data G d CPoly) :
    eval v (lossPoly X) = 1-rawWinning (evaluate v X) := by
  change eval v (sub (constant 1) (winningPoly X).1) = _
  rw [eval_sub,eval_constant]
  simpa only [ceval, Rat.cast_one] using congrArg (1- ·) (winningPoly_eval v X)

def identity (d : ℕ) : Matrix (Fin d) (Fin d) CPoly := fun i j => if i=j then cone else czero
@[simp] theorem eval_identity (v : ℕ → ℝ) (d : ℕ) : evalMatrix v (identity d) = 1 := by
  funext i j
  by_cases h : i=j <;> simp [evalMatrix,identity,Matrix.one_apply,h]

def constraints {G : BCSGame} {d : ℕ} (X Y : Data G d CPoly) (eps : ℚ) : Sentence :=
  let E := enumFin d
  let D := enumProd E E
  matrixEq D X.rho (gram D Y.rho) ++ ceq (tr D X.rho) cone ++
  all (enumFin G.contexts) (fun c =>
    all (enumFixed (Fin G.numVars → Bool)) (fun a => matrixEq E (X.alice c a) (gram E (Y.alice c a))) ++
    matrixEq E (fun i j => total (enumFixed (Fin G.numVars → Bool)) fun a => X.alice c a i j) (identity d)) ++
  all (enumFin G.numVars) (fun w =>
    all (enumFixed Bool) (fun b => matrixEq E (X.bob w b) (gram E (Y.bob w b))) ++
    matrixEq E (fun i j => total (enumFixed Bool) fun b => X.bob w b i j) (identity d)) ++
  [(false,sub (constant eps) (lossPoly X))]

theorem evalMatrix_total {ι : Type} [Fintype ι] {d : ℕ} (v : ℕ → ℝ)
    (E : Enumeration ι) (F : ι → Matrix (Fin d) (Fin d) CPoly) :
    evalMatrix v (fun i j => total E fun a => F a i j) = ∑ a, evalMatrix v (F a) := by
  funext i j
  simp [evalMatrix,Matrix.sum_apply]

set_option backward.isDefEq.respectTransparency false in
theorem models_constraints {G : BCSGame} {d : ℕ} (v : ℕ → ℝ)
    (X Y : Data G d CPoly) (eps : ℚ) : Models v (constraints X Y eps) ↔
    (evaluate v X).rho = (evaluate v Y).rho.conjTranspose * (evaluate v Y).rho ∧
    Matrix.trace (evaluate v X).rho = 1 ∧
    (∀ c, (∀ a, (evaluate v X).alice c a = ((evaluate v Y).alice c a).conjTranspose * (evaluate v Y).alice c a) ∧
      ∑ a, (evaluate v X).alice c a = 1) ∧
    (∀ w, (∀ b, (evaluate v X).bob w b = ((evaluate v Y).bob w b).conjTranspose * (evaluate v Y).bob w b) ∧
      ∑ b, (evaluate v X).bob w b = 1) ∧
    1-rawWinning (evaluate v X) ≤ eps := by
  classical
  simp only [constraints,models_append,models_matrixEq,eval_gram,models_ceq,ceval_tr,
    ceval_one,models_all,eval_identity]
  simp! only [evalMatrix_total,eval_identity]
  have hl : Models v [(false,sub (constant eps) (lossPoly X))] ↔
      1-rawWinning (evaluate v X) ≤ eps := by
    simp [Models,holds,sub_nonneg]
  rw [hl]
  simp only [and_assoc]
  rfl

/-- Every decoded satisfying tuple is an original mixed density / arbitrary POVM strategy. -/
theorem strategy_of_models {G : BCSGame} {d : ℕ} (v : ℕ → ℝ)
    (X Y : Data G d CPoly) (eps : ℚ) (h : Models v (constraints X Y eps)) :
    ∃ s : Strategy G d, loss s ≤ eps := by
  obtain ⟨hρ,ht,hA,hB,hl⟩ := (models_constraints v X Y eps).mp h
  let s : Strategy G d := {
    rho := (evaluate v X).rho
    rho_positive := (positive_iff_factor _).mpr ⟨_,hρ⟩
    rho_trace := ht
    alice := (evaluate v X).alice
    alice_positive := fun c a => (positive_iff_factor _).mpr ⟨_,(hA c).1 a⟩
    alice_complete := fun c => (hA c).2
    bob := (evaluate v X).bob
    bob_positive := fun w b => (positive_iff_factor _).mpr ⟨_,(hB w).1 b⟩
    bob_complete := fun w => (hB w).2 }
  exact ⟨s,hl⟩

abbrev Entry (G : BCSGame) (d : ℕ) := Bool ×
  (((Fin d × Fin d) × (Fin d × Fin d)) ⊕
   ((Fin G.contexts × (Fin G.numVars → Bool) × Fin d × Fin d) ⊕
    (Fin G.numVars × Bool × Fin d × Fin d)))

def symbols (G : BCSGame) (d : ℕ) (b : Bool) : Data G d CPoly where
  rho i j := cvar (Encodable.encode ((b,Sum.inl (i,j)) : Entry G d))
  alice c a i j := cvar (Encodable.encode ((b,Sum.inr (Sum.inl (c,a,i,j))) : Entry G d))
  bob w a i j := cvar (Encodable.encode ((b,Sum.inr (Sum.inr (w,a,i,j))) : Entry G d))

def sentence (G : BCSGame) (eps : ℚ) (d : ℕ) : Sentence :=
  if d=0 then [(false,constant (-1))] else constraints (symbols G d false) (symbols G d true) eps

def dataVal {G : BCSGame} {d : ℕ} (X Y : Data G d ℂ) : Entry G d → ℂ
  | (b,Sum.inl (i,j)) => if b then Y.rho i j else X.rho i j
  | (b,Sum.inr (Sum.inl (c,a,i,j))) => if b then Y.alice c a i j else X.alice c a i j
  | (b,Sum.inr (Sum.inr (w,a,i,j))) => if b then Y.bob w a i j else X.bob w a i j

theorem data_ext {G : BCSGame} {d : ℕ} {K : Type*} (X Y : Data G d K)
    (hρ : X.rho = Y.rho) (hA : X.alice = Y.alice) (hB : X.bob = Y.bob) : X = Y := by
  cases X; cases Y; cases hρ; cases hA; cases hB; rfl

@[simp] theorem evaluate_symbols {G : BCSGame} {d : ℕ} (X Y : Data G d ℂ) :
    evaluate (valuation (dataVal X Y)) (symbols G d false) = X ∧
    evaluate (valuation (dataVal X Y)) (symbols G d true) = Y := by
  constructor <;> apply data_ext <;> funext
  all_goals simp only [evaluate,symbols,evalMatrix,ceval_cvar_valuation]
  all_goals rfl

/-- Exact existential ordered-ring reduction, including rational equality at the boundary. -/
theorem truth_iff_feasible (G : BCSGame) (eps : ℚ) (d : ℕ) :
    Truth (sentence G eps d) ↔ Feasible G eps d := by
  classical
  by_cases hd : d=0
  · subst d
    simp [sentence,Truth,holds,Feasible]
  · simp only [sentence,hd,↓reduceIte]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨Nat.pos_of_ne_zero hd,strategy_of_models v _ _ eps hv⟩
    · rintro ⟨_,s,hs⟩
      let X : Data G d ℂ := ⟨s.rho,s.alice,s.bob⟩
      obtain ⟨R,hR⟩ := (positive_iff_factor s.rho).mp s.rho_positive
      have hA : ∀ c a, ∃ Y, s.alice c a = Y.conjTranspose * Y :=
        fun c a => (positive_iff_factor _).mp (s.alice_positive c a)
      choose A hA using hA
      have hB : ∀ w b, ∃ Y, s.bob w b = Y.conjTranspose * Y :=
        fun w b => (positive_iff_factor _).mp (s.bob_positive w b)
      choose B hB using hB
      let Y : Data G d ℂ := ⟨R,A,B⟩
      refine ⟨valuation (dataVal X Y),?_⟩
      apply (models_constraints _ _ _ _).mpr
      rw [(evaluate_symbols X Y).1,(evaluate_symbols X Y).2]
      exact ⟨hR,s.rho_trace,fun c => ⟨hA c,s.alice_complete c⟩,
        fun w => ⟨hB w,s.bob_complete w⟩,hs⟩

end
end E2.FeasibilitySentence

