import E2.CompilerUpperBase
import E2.CompilerNormalizedCorner

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerTensor E2.CompilerBoolean
open E2.CompilerMultiSelector E2.FiniteConstruction Companion.Analytic
variable {ι : Type*} {d n : ℕ}

@[simp] theorem rational_smul (c : ℚ) (M : Mat d) : c • M = (c:ℂ) • M :=
  (IsScalarTower.algebraMap_smul ℂ c M).symm

/-- The rational algebra atom is the concrete complex matrix atom. -/
theorem rational_atom (X : Mat d) (b : Bool) :
    E2.CompilerMultiSelector.atom X b = E2.CompilerBoolean.atom X b := by
  cases b <;> simp [E2.CompilerMultiSelector.atom,E2.CompilerBoolean.atom]

/-- Orthogonality of joint assignments, with the fixed original product order. -/
theorem joint_mul (x : Fin n → Mat d) (hx : ∀ i, Domain.reflection.Holds (x i))
    (hc : ∀ i j, Commute (x i) (x j)) (a b : Fin n → Bool) :
    E2.CompilerBoolean.joint x a * E2.CompilerBoolean.joint x b =
      if a=b then E2.CompilerBoolean.joint x a else 0 := by
  simpa only [E2.CompilerRealize.joint,rational_atom,E2.CompilerBoolean.joint] using
    selector_orthogonality x (fun i => (hx i).2) hc a b

/-- Reflection-word normalization applies to the concrete matrix assignment. -/
theorem normalForm_eval {κ : Type*} (x : κ → Mat d)
    (hx : ∀ i, Domain.reflection.Holds (x i)) (p : Poly κ) :
    linearSum x (E2.CompilerWords.normalForm p)=Poly.eval x p := by
  simpa only [linearSum,rational_smul,word,E2.CompilerWords.sumEval,E2.CompilerWords.wordEval] using
    E2.CompilerWords.eval_normalForm x hx p


variable [Fintype ι]

def baseWord (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r : Fin P.relations.length) :=
  (List.ofFn (baseControl P s r)).prod

def signedSource (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (t : Letter (ι × Fin 2) n) : Mat (registerSize P*d) :=
  if t.positive then t.source.elim 1 (baseSource P s) else -(t.source.elim 1 (baseSource P s))

theorem signedSource_joint (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) (t : Letter (ι × Fin 2) (q P r)) (a : Fin (q P r) → Bool) :
    Commute (signedSource P s t) (E2.CompilerBoolean.joint (baseZ P r) a) := by
  have h (k) := commute_joint (baseSource P s k) (baseZ P r) (baseSourceZ P s k r) a
  unfold signedSource
  cases hp : t.positive <;> cases hs : t.source <;>
    simp only [hp,↓reduceIte,hs,Option.elim_none,Option.elim_some]
  · exact (Commute.one_left _).neg_left
  · exact (h _).neg_left
  · exact Commute.one_left _
  · exact h _

theorem base_word_routing (P : Presentation ι) (s : ι × Fin 2 → Mat d) (r : Fin P.relations.length) :
    baseWord P s r = blockSum (E2.CompilerBoolean.joint (baseZ P r))
      (fun a => signedWord (baseSource P s)
        ((packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[]))) := by
  have he : List.ofFn (baseControl P s r) =
      (letters (relationWords P r)).map (fun t =>
        E2.CompilerMultiSelector.control (E2.CompilerBoolean.joint (baseZ P r) t.selector) (signedSource P s t)) := by
    have hh := List.ofFn_comp' (letters (relationWords P r)).get
      (fun t => E2.CompilerMultiSelector.control (E2.CompilerBoolean.joint (baseZ P r) t.selector) (signedSource P s t))
    rw [List.ofFn_get] at hh
    change List.ofFn (fun i => E2.CompilerMultiSelector.control
      (E2.CompilerBoolean.joint (baseZ P r) ((letters (relationWords P r)).get i).selector)
      (signedSource P s ((letters (relationWords P r)).get i))) = _
    exact hh
  unfold baseWord
  rw [he]
  have h := controlled_word_blocks (E2.CompilerBoolean.joint (baseZ (d:=d) P r))
    (E2.CompilerBoolean.joint_partition _) (joint_mul _ (baseZ_domain P r) (baseZZ P r))
    ((letters (relationWords P r)).map (fun t => (t.selector,signedSource P s t))) (by
      intro t ht a
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
      exact signedSource_joint P s r u a)
  simp only [List.map_map,Function.comp_def] at h
  rw [h]
  congr 1
  funext a
  convert letters_block (baseSource P s) (relationWords P r) a using 1 <;>
    simp only [signedSource,q] <;> rfl

theorem base_anticommutator (P : Presentation ι) (r : Fin P.relations.length) (i : Fin (q P r)) :
    baseX (d:=d) P r i*baseZ P r i+baseZ P r i*baseX P r i=0 := by
  have h := baseXZ_conjugate (d:=d) P r i i
  rw [ite_eq_left rfl] at h
  have hh := congrArg (fun M => M*baseX P r i) h
  have he : baseX (d:=d) P r i*baseZ P r i=-(baseZ P r i*baseX P r i) := by
    simpa only [mul_assoc,(baseX_domain P r i).2,mul_one,neg_mul] using hh
  rw [he,neg_add_cancel]

theorem base_compression (P : Presentation ι) (r : Fin P.relations.length)
    (a : Fin (q P r) → Bool) :
    decodeProjection (baseE (d:=d) P r)*E2.CompilerBoolean.joint (baseZ P r) a*
      decodeProjection (baseE P r) = ((1/2:ℚ)^(q P r)) • decodeProjection (baseE P r) := by
  simp only [baseE,decode_encode_projection]
  simpa only [rational_atom,E2.CompilerBoolean.joint] using
    pauli_multi_compression (baseX (d:=d) P r) (baseZ P r)
      (fun i => (baseX_domain P r i).2) (base_anticommutator P r)
      (fun i j _ => baseXX P r i j) (baseXZ P r) a

theorem signedWord_E (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (r : Fin P.relations.length) (t : Bool × List (ι × Fin 2)) :
    Commute (signedWord (baseSource P s) t) (decodeProjection (baseE P r)) := by
  have hk (k) : Commute (baseSource P s k) (decodeProjection (baseE P r)) := by
    simp only [baseE,decode_encode_projection]
    exact commute_joint _ _ (baseSourceX P s k r) _
  have hw : Commute (word (baseSource P s) t.2) (decodeProjection (baseE P r)) := by
    apply Commute.list_prod_left
    intro M hM
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hM
    exact hk k
  unfold signedWord
  split_ifs
  · exact hw
  · exact hw.neg_left

/-- Exact normalized compression in the upper matrices, before imposing any game relation. -/
theorem base_normalized_corner (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (hs : ∀ k, Domain.reflection.Holds (s k)) (r : Fin P.relations.length) :
    decodeProjection (baseE P r)*baseWord P s r*decodeProjection (baseE P r) =
      normalization P r • (E2.CompilerTensor.source (registerSize P)
        (Poly.eval s (CompilerFrontend.substitute (CompilerFrontend.replacement P) (P.relations.get r)))*
        decodeProjection (baseE P r)) := by
  let e := decodeProjection (baseE (d:=d) P r)
  let W := fun a : Fin (q P r) → Bool => signedWord (baseSource P s)
    ((packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[]))
  have hc (a) : Commute (W a) e := signedWord_E P s r _
  have hsum : (∑ a, W a) = (2*(denominator (relationWords P r):ℚ)) •
      E2.CompilerTensor.source (registerSize P)
        (Poly.eval s (CompilerFrontend.substitute (CompilerFrontend.replacement P) (P.relations.get r))) := by
    rw [show (∑ a, W a) = (2*(denominator (relationWords P r):ℚ)) •
        linearSum (baseSource P s) (relationWords P r) from packed_selector_sum _ _]
    congr 1
    rw [relationWords,normalForm_eval (baseSource P s)
      (fun k => source_reflection _ (hs k))]
    exact eval_source s _
  change e*baseWord P s r*e=normalization P r • (_*e)
  calc
    _ = ∑ a, e*E2.CompilerBoolean.joint (baseZ P r) a*W a*e := by
      rw [base_word_routing]
      simp only [blockSum,Finset.mul_sum,Finset.sum_mul,mul_assoc]
      rfl
    _ = ∑ a, ((1/2:ℚ)^(q P r)) • (W a*e) := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = (e*E2.CompilerBoolean.joint (baseZ P r) a*e)*W a := by
          rw [mul_assoc,mul_assoc,(hc a).eq]
          simp only [mul_assoc]
        _ = _ := by rw [base_compression]; rw [Algebra.smul_mul_assoc,(hc a).eq]
    _ = ((1/2:ℚ)^(q P r)) • ((∑ a, W a)*e) := by
      rw [← Finset.smul_sum,Finset.sum_mul]
    _ = _ := by
      rw [hsum,Algebra.smul_mul_assoc,smul_smul]
      congr 1
      unfold normalization
      rw [div_pow]
      simp only [one_pow]
      ring

end
end E2.CompilerUpper
