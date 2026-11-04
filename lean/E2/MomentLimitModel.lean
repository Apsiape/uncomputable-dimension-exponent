import E2.MomentGNS

namespace E2.ExactCompactness
noncomputable section
open Filter
variable {ι : Type*} {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]

structure MomentSequence (P : Presentation ι) (B : ℕ → Type*) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)] where
  functional : ∀ n, B n →ₗ[ℂ] ℂ
  bounded : ∀ n a, ‖functional n a‖≤4*‖a‖
  hermitian : ∀ n a, functional n (star a)=star (functional n a)
  positive : ∀ n a, 0≤(functional n (star a*a)).re
  normalized : ∀ n, functional n 1=1
  tuple : ∀ n, ι → B n
  tuple_norm : ∀ n j, ‖tuple n j‖≤1
  domains : ∀ n j, (P.domain j).HoldsC (tuple n j)
  central : ∀ j (a : BoundedProduct B), Tendsto
    (fun n => functional n (tuple n j*a n)-functional n (a n*tuple n j)) atTop (nhds 0)
  relations : ∀ r ∈ P.relations, Tendsto
    (fun n => functional n (star (r.evalC (tuple n))*r.evalC (tuple n))) atTop (nhds 0)

def sequenceFunctional {P : Presentation ι} (s : MomentSequence P B) : BoundedProduct B →L[ℂ] ℂ :=
  limitFunctional s.functional 4 (by norm_num) s.bounded (Ultrafilter.of atTop)

theorem sequenceFunctional_tendsto {P : Presentation ι} (s : MomentSequence P B) (a : BoundedProduct B) :
    Tendsto (fun n => s.functional n (a n)) ((Ultrafilter.of (atTop : Filter ℕ) : Ultrafilter ℕ) : Filter ℕ) (nhds (sequenceFunctional s a)) :=
  limitValue_tendsto s.functional 4 (by norm_num) s.bounded (Ultrafilter.of atTop) a

theorem sequenceFunctional_star {P : Presentation ι} (s : MomentSequence P B) (a : BoundedProduct B) :
    sequenceFunctional s (star a)=star (sequenceFunctional s a) :=
  limitFunctional_star s.functional 4 (by norm_num) s.bounded s.hermitian (Ultrafilter.of atTop) a

def sequenceCentralizer {P : Presentation ι} (s : MomentSequence P B) : StarSubalgebra ℂ (BoundedProduct B) :=
  centralizer (sequenceFunctional s) (sequenceFunctional_star s)

instance sequenceCentralizer_closed {P : Presentation ι} (s : MomentSequence P B) :
    IsClosed (sequenceCentralizer s : Set (BoundedProduct B)) := inferInstanceAs
      (IsClosed (centralizer (sequenceFunctional s) (sequenceFunctional_star s) : Set (BoundedProduct B)))

def sequenceTrace {P : Presentation ι} (s : MomentSequence P B) : TracialState (sequenceCentralizer s) :=
  centralizerState (sequenceFunctional s) (sequenceFunctional_star s)
    (limitFunctional_positive s.functional 4 (by norm_num) s.bounded s.positive (Ultrafilter.of atTop))
    (limitFunctional_one s.functional 4 (by norm_num) s.bounded s.normalized (Ultrafilter.of atTop))

def sequenceRawTuple {P : Presentation ι} (s : MomentSequence P B) : ι → BoundedProduct B :=
  boundedTuple s.tuple s.tuple_norm

theorem sequenceTuple_central {P : Presentation ι} (s : MomentSequence P B) (j : ι) :
    sequenceRawTuple s j ∈ sequenceCentralizer s := by
  intro a
  have ht := (sequenceFunctional_tendsto s (sequenceRawTuple s j*a)).sub
    (sequenceFunctional_tendsto s (a*sequenceRawTuple s j))
  have hz := (s.central j a).mono_left (Ultrafilter.of_le atTop)
  exact sub_eq_zero.mp (tendsto_nhds_unique ht hz)

def sequenceTuple {P : Presentation ι} (s : MomentSequence P B) (j : ι) : sequenceCentralizer s :=
  ⟨sequenceRawTuple s j,sequenceTuple_central s j⟩

theorem sequenceTuple_domains {P : Presentation ι} (s : MomentSequence P B) (j : ι) :
    (P.domain j).HoldsC (sequenceTuple s j) :=
  closedSubalgebra_domain _ _ _ (boundedTuple_domain P.domain s.tuple s.tuple_norm s.domains j)

theorem sequence_relation_square {P : Presentation ι} (s : MomentSequence P B) (r : Poly ι) (hr : r∈P.relations) :
    (sequenceTrace s).toLinearMap (star (r.evalC (sequenceTuple s))*r.evalC (sequenceTuple s))=0 := by
  have ht := sequenceFunctional_tendsto s
    (star (r.evalC (sequenceRawTuple s))*r.evalC (sequenceRawTuple s))
  have hz := (s.relations r hr).mono_left (Ultrafilter.of_le atTop)
  have hcoord : (fun n => s.functional n ((star (r.evalC (sequenceRawTuple s))*r.evalC (sequenceRawTuple s)) n))=
      (fun n => s.functional n (star (r.evalC (s.tuple n))*r.evalC (s.tuple n))) := by
    funext n
    simp only [lp.infty_coeFn_mul,Pi.mul_apply,lp.coeFn_star,Pi.star_apply,coordinate_polynomial]
    rfl
  rw [hcoord] at ht
  have hzero := tendsto_nhds_unique ht hz
  have he : ((r.evalC (sequenceTuple s) : sequenceCentralizer s) : BoundedProduct B)=r.evalC (sequenceRawTuple s) := by
    exact (ExactTrace.eval_map (sequenceCentralizer s).subtype (sequenceTuple s) r).symm
  change sequenceFunctional s (star ((r.evalC (sequenceTuple s) : sequenceCentralizer s) : BoundedProduct B)*
    ((r.evalC (sequenceTuple s) : sequenceCentralizer s) : BoundedProduct B))=0
  rw [he]
  exact hzero

def limitExactModel {P : Presentation ι} (s : MomentSequence P B) :
    ExactModel P (ExactTrace.FaithfulGNSAlgebra (sequenceTrace s)) :=
  exactModelOfMoments P (sequenceTrace s) (sequenceTuple s) (sequenceTuple_domains s) (sequence_relation_square s)

theorem limit_upper {P : Presentation ι} (s : MomentSequence P B) (r : Poly ι)
    (hsa : IsSelfAdjoint (r.evalC (sequenceTuple s))) (c : ℝ)
    (hc : ∀ n, (s.functional n (r.evalC (s.tuple n))).re≤c) :
    ((limitExactModel s).state.toLinearMap (r.evalC (limitExactModel s).value)).re≤c := by
  have hp := exactModelOfMoments_preserves P (sequenceTrace s) (sequenceTuple s)
    (sequenceTuple_domains s) (sequence_relation_square s) r hsa
  change ((exactModelOfMoments P (sequenceTrace s) (sequenceTuple s)
    (sequenceTuple_domains s) (sequence_relation_square s)).state.toLinearMap
      (r.evalC (exactModelOfMoments P (sequenceTrace s) (sequenceTuple s)
        (sequenceTuple_domains s) (sequence_relation_square s)).value)).re≤c
  rw [hp]
  have he : ((r.evalC (sequenceTuple s) : sequenceCentralizer s) : BoundedProduct B)=r.evalC (sequenceRawTuple s) :=
    (ExactTrace.eval_map (sequenceCentralizer s).subtype (sequenceTuple s) r).symm
  change (sequenceFunctional s (↑(r.evalC (sequenceTuple s)))).re≤c
  rw [he]
  apply le_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (sequenceFunctional_tendsto s (r.evalC (sequenceRawTuple s))))
  apply Eventually.of_forall
  intro n
  simpa only [Function.comp_def,coordinate_polynomial,sequenceRawTuple,boundedTuple] using hc n

end
end E2.ExactCompactness
