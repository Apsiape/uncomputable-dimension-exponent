import E2.BooleanBridgeData
import E2.BooleanReferencePVM

namespace E2.BooleanBridgeData
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
open E2.CompilerStrategy E2.BooleanExtraction E2.CompilerDomains
open BooleanRealignment BooleanGameLoss
variable {G : BCSGame} {d : ℕ}

theorem legalPVM_value (s : Strategy G d) (c x) :
    (legalPVM s).value c x = ∑ y, if legalize G c y = x then alice s c y else 0 := by
  change (∑ i : Fin (Fintype.card (Fin G.numVars → Bool)),
    if legalize G c ((Fintype.equivFin _).symm i) = x then
      alice s c ((Fintype.equivFin _).symm i) else 0) = _
  exact (Fintype.equivFin (Fin G.numVars → Bool)).symm.sum_comp
    (fun y => if legalize G c y = x then alice s c y else 0)

theorem alice_signed (s : Strategy G d) (c v) :
    contextValue (legalPVM s) c v =
      ∑ x, bitSign (legalize G c x v) • alice s c x := by
  rw [context_signed]
  simp_rw [legalPVM_value,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [smul_ite,smul_zero]
  simp

def reflection (s : Strategy G d) (v : Fin G.numVars) : Mat (bdim d) :=
  encodeProjection (bob s v true)

theorem reflection_domain (s : Strategy G d) (v) : Domain.reflection.Holds (reflection s v) :=
  encode_projection _ (bob_projection s v true)

theorem bob_signed (s : Strategy G d) (v) :
    reflection s v = ∑ b, bitSign b • bob s v b := by
  have he := bob_sum s v
  simp only [Fintype.sum_bool] at he
  simp [Fintype.sum_bool,bitSign]
  unfold reflection encodeProjection
  rw [← he]
  module

def good (s : Strategy G d) (c : Fin G.contexts) (v : Fin G.numVars) : ℝ :=
  ∑ x, ∑ b, if legalize G c x v = b then outcome s c v x b else 0

theorem good_ge (s : Strategy G d) (c v) :
    (∑ x ∈ G.allowed c, outcome s c v x (x v)) ≤ good s c v := by
  calc
    _ ≤ ∑ x ∈ G.allowed c, ∑ b, if legalize G c x v = b then outcome s c v x b else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      have he : legalize G c x = x := by simp [legalize,hx]
      simp only [he]
      simp
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x hx hn => Finset.sum_nonneg (fun b hb => by
        split_ifs
        · exact outcome_nonneg s c v x b
        · exact le_rfl))

theorem signed_trace (s : Strategy G d) (c v) :
    (Matrix.trace (rho s * Matrix.kronecker (contextValue (legalPVM s) c v)
      (reflection s v))).re = 2 * good s c v - 1 := by
  have hm : Matrix.kronecker (contextValue (legalPVM s) c v) (reflection s v) =
      ∑ x, ∑ b, (bitSign (legalize G c x v) * bitSign b) •
        Matrix.kronecker (alice s c x) (bob s v b) := by
    rw [alice_signed,bob_signed]
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sum_apply,
      Matrix.smul_apply,smul_eq_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [hm]
  simp only [Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,smul_eq_mul,correlation]
  have hs (x : Fin G.numVars → Bool) (b : Bool) :
      ((bitSign (legalize G c x v) * bitSign b) *
        Matrix.trace (s.rho * Matrix.kronecker (s.alice c x) (s.bob v b))).re =
      2 * (if legalize G c x v = b then outcome s c v x b else 0) - outcome s c v x b := by
    cases h : legalize G c x v <;> cases b <;> simp [bitSign,h,outcome] <;> ring
  simp_rw [hs]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,outcome_sum,good]

theorem consistency_bound_sq (s : Strategy G d) (c v) :
    hs (reflection s v * BooleanMixedAmplitude.amplitude (rho s) -
      BooleanMixedAmplitude.amplitude (rho s) *
        contextValue (referencePVM (d := bdim d) (legalPVM s)) c v)^2 ≤
        4 * localLoss s c v := by
  have hX : Domain.reflection.Holds (contextValue (legalPVM s) c v) :=
    (ContextRepresentation.ofPVM (legalPVM s)).domains c v
  rw [reference_value,consistency_squared (rho s) (rho_positive s) (rho_trace s)
    _ _ hX (reflection_domain s v)]
  have ht : (Matrix.trace (rho s * Matrix.kroneckerMap (fun x y : ℂ => x*y)
      (contextValue (legalPVM s) c v) (reflection s v))).re = 2 * good s c v - 1 :=
    signed_trace s c v
  rw [ht]
  have hh := good_ge s c v
  dsimp only [localLoss]
  linarith

end
end E2.BooleanBridgeData
