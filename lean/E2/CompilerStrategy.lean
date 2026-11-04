import E2.CompilerFlat
import E2.CompilerDomains

namespace E2.CompilerStrategy
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Companion.Analytic E2.FiniteConstruction
variable {d : ℕ}

def bellVector (d : ℕ) : Fin d × Fin d → ℂ := fun i => if i.1=i.2 then 1 else 0

def bell (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (d : ℂ)⁻¹ • Matrix.vecMulVec (bellVector d) (star (bellVector d))

theorem bell_positive (d : ℕ) : (bell d).PosSemidef := by
  apply (Matrix.posSemidef_vecMulVec_self_star (bellVector d)).smul
  exact inv_nonneg.mpr (by exact_mod_cast Nat.zero_le d)

theorem bell_trace (hd : 0 < d) : (bell d).trace=1 := by
  have hn : (d:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simp [bell,bellVector,Matrix.trace,Matrix.diag,Matrix.vecMulVec,
    Fintype.sum_prod_type,hn]

/-- The transpose is on Alice's operator; all matrices may be complex. -/
theorem bell_pairing (A B : Mat d) :
    ((bell d)*Matrix.kronecker A.transpose B).trace = (d:ℂ)⁻¹ * (A*B).trace := by
  simp only [bell,Matrix.smul_mul,Matrix.trace_smul]
  congr 1
  simp [Matrix.trace,Matrix.mul_apply,Matrix.vecMulVec,
    Matrix.of_apply,bellVector,Fintype.sum_prod_type,apply_ite]

/-- A PVM labeled by the original game's total Boolean assignments.
Illegal assignments have zero operators. -/
structure ContextPVM (G : BCSGame) (d : ℕ) where
  value : Fin G.contexts → (Fin G.numVars → Bool) → Mat d
  hermitian : ∀ c a, (value c a).conjTranspose=value c a
  multiply : ∀ c a b, value c a*value c b=if a=b then value c a else 0
  complete : ∀ c, ∑ a, value c a=1
  legal : ∀ c a, a ∉ G.allowed c → value c a=0

variable {G : BCSGame}

theorem ContextPVM.projection (A : ContextPVM G d) (c) (a) :
    Domain.projection.Holds (A.value c a) := by
  exact ⟨A.hermitian c a,by simpa using A.multiply c a a⟩

theorem projection_positive (P : Mat d) (hP : Domain.projection.Holds P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  simpa only [hP.1,hP.2] using h

def ContextPVM.marginal (A : ContextPVM G d) (c : Fin G.contexts) (v : Fin G.numVars) : Mat d :=
  ∑ a, if a v then A.value c a else 0

theorem ContextPVM.marginal_projection (A : ContextPVM G d) (c) (v) :
    Domain.projection.Holds (A.marginal c v) := by
  classical
  constructor
  · simp only [ContextPVM.marginal,Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp [A.hermitian]
  · simp only [ContextPVM.marginal,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a v=true
    · simp only [h,↓reduceIte]
      simp only [ite_mul,Matrix.zero_mul,A.multiply]
      rw [Finset.sum_eq_single a]
      · simp [h]
      · intro b _ hb
        simp [hb]
      · simp
    · simp [h]

/-- Push finite local PVM outcomes into the original game's total assignment
labels. Coincident labels are combined, so no artificial injectivity is needed. -/
def ContextPVM.ofOutcomes (k : Fin G.contexts → ℕ)
    (M : (c : Fin G.contexts) → Fin (k c) → Mat d)
    (label : (c : Fin G.contexts) → Fin (k c) → (Fin G.numVars → Bool))
    (hM : ∀ c i, Domain.projection.Holds (M c i))
    (hmul : ∀ c i j, M c i*M c j=if i=j then M c i else 0)
    (hsum : ∀ c, ∑ i, M c i=1)
    (hlegal : ∀ c i, label c i ∈ G.allowed c) : ContextPVM G d where
  value c a := ∑ i, if label c i=a then M c i else 0
  hermitian c a := by
    simp only [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [(hM c i).1]
  multiply c a b := by
    classical
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have ht (i : Fin (k c)) :
        (∑ j, (if label c i=a then M c i else 0)*(if label c j=b then M c j else 0)) =
          if label c i=a then (if label c i=b then M c i else 0) else 0 := by
      by_cases hi : label c i=a
      · simp only [ite_eq_left hi,mul_ite,Matrix.mul_zero,hmul]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [Ne.symm hj]
        · simp
      · simp [hi]
    simp_rw [ht]
    by_cases hab : a=b
    · subst b
      simp only [ite_true]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : label c i=a <;> simp [hi]
    · simp only [ite_eq_right hab]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : label c i=a
      · have hj : label c i ≠ b := by simpa [hi] using hab
        simp [hi,hab]
      · simp [hi]
  complete c := by
    rw [Finset.sum_comm]
    simpa using hsum c
  legal c a ha := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : label c i ≠ a := by
      intro h
      exact ha (h ▸ hlegal c i)
    simp [hi]

def ContextPVM.strategy (A : ContextPVM G d) (hd : 0 < d)
    (Q : Fin G.numVars → Mat d) (hQ : ∀ v, Domain.projection.Holds (Q v)) : Strategy G d where
  rho := bell d
  rho_positive := bell_positive d
  rho_trace := bell_trace hd
  alice c a := (A.value c a).transpose
  alice_positive c a := Matrix.posSemidef_transpose_iff.mpr (projection_positive _ (A.projection c a))
  alice_complete c := by simpa only [← Matrix.transpose_sum,Matrix.transpose_one] using congrArg Matrix.transpose (A.complete c)
  bob v b := if b then Q v else 1-Q v
  bob_positive v b := by
    cases b
    · exact projection_positive _ (projection_complement (hQ v))
    · exact projection_positive _ (hQ v)
  bob_complete v := by simp

/-- A legal context PVM and Bob projections produce the original unrestricted
`Strategy`, with its original density matrix and assignment indexing. -/
theorem strategy_pairing (A : ContextPVM G d) (hd : 0<d)
    (Q : Fin G.numVars → Mat d) (hQ : ∀ v, Domain.projection.Holds (Q v)) (c) (v) (a) :
    (Matrix.trace ((A.strategy hd Q hQ).rho *
      Matrix.kronecker ((A.strategy hd Q hQ).alice c a)
        ((A.strategy hd Q hQ).bob v (a v)))).re =
      ((d:ℂ)⁻¹ * (A.value c a * (if a v then Q v else 1-Q v)).trace).re := by
  exact congrArg Complex.re (bell_pairing _ _)

/-- The full assignment sum, with legality retained, is precisely the binary
agreement operator for the context marginal. -/
theorem ContextPVM.agreement_operator (A : ContextPVM G d) (c) (v) (Q : Mat d) :
    (∑ a ∈ G.allowed c, A.value c a * (if a v then Q else 1-Q)) =
      A.marginal c v*Q + (1-A.marginal c v)*(1-Q) := by
  classical
  have hext : (∑ a ∈ G.allowed c, A.value c a * (if a v then Q else 1-Q)) =
      ∑ a, A.value c a * (if a v then Q else 1-Q) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ ha
    rw [A.legal c a ha,Matrix.zero_mul]
  rw [hext]
  have hsplit : (∑ a, if a v then A.value c a else 0) +
      (∑ a, if a v then 0 else A.value c a) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert A.complete c using 1
    apply Finset.sum_congr rfl
    intro a _
    cases a v <;> simp
  have hfalse : (∑ a, if a v then 0 else A.value c a)=1-A.marginal c v := by
    unfold ContextPVM.marginal
    exact eq_sub_of_add_eq' hsplit
  rw [← hfalse]
  simp only [ContextPVM.marginal,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases a v <;> simp

theorem projection_disagreement (hd : 0<d) (P Q : Mat d)
    (hP : Domain.projection.Holds P) (hQ : Domain.projection.Holds Q) :
    ((d:ℂ)⁻¹ * (P*Q+(1-P)*(1-Q)).trace).re =
      1-weighted (flatState d hd) (P-Q)^2 := by
  have hn : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hc : (d:ℂ)⁻¹=Complex.ofReal ((d:ℝ)⁻¹) := by simp
  rw [CompilerFlat.flat_state_weighted_square,hsNorm_sq,hsSquared_trace]
  rw [Matrix.conjTranspose_sub,hP.1,hQ.1]
  have hdiff : (P-Q)*(P-Q)=P+Q-P*Q-Q*P := by
    noncomm_ring [hP.2,hQ.2]
  rw [hdiff]
  have hagree : P*Q+(1-P)*(1-Q)=1-P-Q+P*Q+P*Q := by noncomm_ring
  rw [hagree]
  simp only [Matrix.trace_add,Matrix.trace_sub,Matrix.trace_one,Complex.add_re,Complex.sub_re]
  rw [Matrix.trace_mul_comm Q P]
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.add_re,Complex.sub_re,Complex.natCast_re,Fintype.card_fin,
    Complex.ofReal_inv,Complex.inv_re,Complex.inv_im,Complex.normSq_ofReal]
  field_simp [hn]
  ring

/-- Exact incidence agreement in the actual maximally entangled strategy. -/
theorem ContextPVM.agreement (A : ContextPVM G d) (hd : 0<d)
    (Q : Fin G.numVars → Mat d) (hQ : ∀ v, Domain.projection.Holds (Q v)) (c) (v) :
    (∑ a ∈ G.allowed c,
      (Matrix.trace ((A.strategy hd Q hQ).rho *
        Matrix.kronecker ((A.strategy hd Q hQ).alice c a)
          ((A.strategy hd Q hQ).bob v (a v)))).re) =
      1-weighted (flatState d hd) (A.marginal c v-Q v)^2 := by
  simp_rw [strategy_pairing]
  rw [← Complex.re_sum,← Finset.mul_sum,← Matrix.trace_sum]
  rw [A.agreement_operator]
  exact projection_disagreement hd _ _ (A.marginal_projection c v) (hQ v)

/-- The original game's loss is the incidence-weighted sum of squared flat
marginal errors. This includes ordinary Boolean predicates and arbitrary scopes. -/
theorem ContextPVM.loss_eq (A : ContextPVM G d) (hd : 0<d)
    (Q : Fin G.numVars → Mat d) (hQ : ∀ v, Domain.projection.Holds (Q v)) :
    loss (A.strategy hd Q hQ) =
      ∑ c, ∑ v, (G.probability c v:ℝ)*
        weighted (flatState d hd) (A.marginal c v-Q v)^2 := by
  have hp : (∑ c, ∑ v, (G.probability c v:ℝ))=1 := by
    exact_mod_cast G.probability_sum
  simp only [loss,winningProbability,A.agreement, mul_sub,mul_one,
    Finset.sum_sub_distrib]
  rw [hp]
  ring

/-- Global quadratic-loss assembly, in the original local dimension. -/
theorem ContextPVM.quadratic_loss (A : ContextPVM G d) (hd : 0<d)
    (Q : Fin G.numVars → Mat d) (hQ : ∀ v, Domain.projection.Holds (Q v))
    (δ C : ℝ) (_hδ : 0≤δ) (_hC : 0≤C)
    (hclose : ∀ c v, v ∈ G.scope c →
      weighted (flatState d hd) (A.marginal c v-Q v) ≤ C*δ) :
    loss (A.strategy hd Q hQ) ≤ C^2*δ^2 := by
  rw [A.loss_eq hd Q hQ]
  have hp : (∑ c, ∑ v, (G.probability c v:ℝ))=1 := by
    exact_mod_cast G.probability_sum
  calc
    _ ≤ ∑ c, ∑ v, (G.probability c v:ℝ)*(C^2*δ^2) := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ G.scope c
      · apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast G.probability_nonneg c v)
        have h := pow_le_pow_left₀ (hsNorm_nonneg _) (hclose c v hv) 2
        change weighted (flatState d hd) (A.marginal c v-Q v)^2 ≤ (C*δ)^2 at h
        simpa only [mul_pow] using h
      · have hz : G.probability c v=0 := by
          by_contra h
          exact hv ((G.probability_support c v).mp h)
        simp [hz]
    _ = C^2*δ^2 := by simp only [← Finset.sum_mul,hp,one_mul]

end
end E2.CompilerStrategy
