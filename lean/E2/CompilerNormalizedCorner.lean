import E2.CompilerWordNormalization

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial
variable {ι : Type*} [Fintype ι]

theorem relationWords_image (P : Presentation ι) (r : Fin P.relations.length) :
    linearSum (fun s => value (tables P) (source P s)) (relationWords P r) =
      image (augmented (realize P)).relations (decodedRelation P r) := by
  have h := normalForm_image (realize P) (fun s => label P (source P s))
    (CompilerFrontend.substitute (CompilerFrontend.replacement P) (P.relations.get r))
  change linearSum (fun s => value (tables P) (source P s)) (relationWords P r) = _ at h
  rw [h]
  apply image_semantic
  intro d x
  simp only [CompilerFrontend.eval_substitute,Poly.eval_var,decodedRelation,sourceDecoder,sourceEmbedding]

theorem realized_packed_routing (P : Presentation ι) (r : Fin P.relations.length) :
    wordValue P r = CompilerMultiSelector.blockSum (selectorValue P r)
      (fun a => signedWord (fun s => value (tables P) (source P s))
        ((packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[]))) := by
  rw [realized_word_routing]
  congr 1
  funext a
  exact letters_block _ _ a

theorem realized_packed_sum (P : Presentation ι) (r : Fin P.relations.length) :
    (∑ a : Fin (q P r) → Bool, signedWord (fun s => value (tables P) (source P s))
      ((packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[]))) =
    (2*(denominator (relationWords P r):ℚ)) •
      image (augmented (realize P)).relations (decodedRelation P r) := by
  exact (packed_selector_sum (fun s => value (tables P) (source P s)) (relationWords P r)).trans
    (congrArg (fun z => (2*(denominator (relationWords P r):ℚ)) • z) (relationWords_image P r))

theorem source_E_commute (P : Presentation ι) (r : Fin P.relations.length) (s : ι × Fin 2) :
    Commute (value (tables P) (source P s))
      (CompilerMultiSelector.atom (value (tables P) (E P r)) true) := by
  rw [selector_and]
  apply CompilerMultiSelector.commute_ordered
  intro i
  exact ((Commute.one_right _).add_right (source_X_commute P r s i)).smul_right (1/2:ℚ)

theorem signedWord_E_commute (P : Presentation ι) (r : Fin P.relations.length)
    (t : Bool × List (ι × Fin 2)) :
    Commute (signedWord (fun s => value (tables P) (source P s)) t)
      (CompilerMultiSelector.atom (value (tables P) (E P r)) true) := by
  have hw : Commute (word (fun s => value (tables P) (source P s)) t.2)
      (CompilerMultiSelector.atom (value (tables P) (E P r)) true) := by
    apply Commute.list_prod_left
    intro y hy
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hy
    exact source_E_commute P r s
  cases hb : t.1 <;> simp only [signedWord,hb,↓reduceIte,Bool.false_eq_true]
  · exact hw.neg_left
  · exact hw

theorem normalized_compression (P : Presentation ι) (r : Fin P.relations.length) :
    CompilerMultiSelector.atom (value (tables P) (E P r)) true * wordValue P r *
      CompilerMultiSelector.atom (value (tables P) (E P r)) true =
    normalization P r • (image (augmented (realize P)).relations (decodedRelation P r) *
      CompilerMultiSelector.atom (value (tables P) (E P r)) true) := by
  let e := CompilerMultiSelector.atom (value (tables P) (E P r)) true
  let W (a : Fin (q P r) → Bool) := signedWord (fun s => value (tables P) (source P s))
    ((packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[]))
  have hc (a) : Commute (W a) e := signedWord_E_commute P r _
  change e*wordValue P r*e = normalization P r • (_*e)
  calc
    _ = ∑ a, e*selectorValue P r a*W a*e := by
      rw [realized_packed_routing]
      simp only [CompilerMultiSelector.blockSum,Finset.mul_sum,Finset.sum_mul,mul_assoc]
      rfl
    _ = ∑ a, ((1/2:ℚ)^(q P r)) • (W a*e) := by
      apply Finset.sum_congr rfl
      intro a _
      calc
        _ = (e*selectorValue P r a*e)*W a := by rw [mul_assoc, mul_assoc, (hc a).eq]; simp only [mul_assoc]
        _ = _ := by rw [realized_compression]; rw [Algebra.smul_mul_assoc,(hc a).eq]
    _ = ((1/2:ℚ)^(q P r)) • ((∑ a, W a)*e) := by
      rw [← Finset.smul_sum,Finset.sum_mul]
    _ = _ := by
      rw [show (∑ a, W a) = (2*(denominator (relationWords P r):ℚ)) •
        image (augmented (realize P)).relations (decodedRelation P r) from realized_packed_sum P r]
      rw [Algebra.smul_mul_assoc,smul_smul]
      congr 1
      unfold normalization
      rw [div_pow]
      simp only [one_pow]
      ring

/-- The remaining normalized corner family, for every original presentation and relation. -/
theorem normalized_corner_certificate (P : Presentation ι) (r : Fin P.relations.length) :
    image (augmented (realize P)).relations (normalizedCornerResidual P r) = 0 := by
  simp only [normalizedCornerResidual,image_sub,image_mul]
  apply sub_eq_zero.mpr
  have hraw := conjugate_corner_substitution P r
  rw [← selector_and] at hraw
  have hsel : image (augmented (realize P)).relations (selectorPolynomial P r) =
      CompilerMultiSelector.atom (value (tables P) (E P r)) true := by
    simp only [selectorPolynomial,CompilerMultiSelector.image_ordered,CompilerMultiSelector.image_atom]
    exact (selector_and P r).symm
  rw [hsel]
  have hcorner : image (augmented (realize P)).relations (cornerPolynomial P r) =
      CompilerMultiSelector.atom (value (tables P) (E P r)) true *
      CompilerMultiSelector.atom (value (tables P) (F P r)) true * wordValue P r := by
    simp only [cornerPolynomial,image_mul,CompilerMultiSelector.image_atom,
      CompilerMultiSelector.image_ordered]
    rfl
  rw [hcorner,hraw,normalized_compression,image_const]
  exact Algebra.smul_def _ _

theorem normalized_corner_weighted (P : Presentation ι) (r : Fin P.relations.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (η : ℝ)
      (m : Model (booleanPresentation (realize P)) d η), 0 ≤ η →
      weighted m.state (Poly.eval m.value (normalizedCornerResidual P r)) ≤ C*η :=
  original_weighted_bound _ _ (normalized_corner_certificate P r)

end
end E2.CompilerNetwork
