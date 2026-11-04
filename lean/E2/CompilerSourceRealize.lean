import E2.CompilerControlRealize

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

/-- Commutators of an arbitrary rational *-polynomial, including every adjoint,
are finite consequences of the variable commutators and exact game domains. -/
theorem substituted_commute {κ : Type*} (G : BCSGame)
    (v : Fin G.numVars) (replacement : κ → Poly (Fin G.numVars))
    (hv : ∀ k, Commute (image (augmented G).relations (replacement k)) (generator G v))
    (p : Poly κ) :
    Commute (image (augmented G).relations (CompilerFrontend.substitute replacement p)) (generator G v) := by
  induction p with
  | const q =>
    change Commute (image (augmented G).relations (.const q)) _
    rw [image_const]
    exact Algebra.commutes q _
  | var k => exact hv k
  | add p q hp hq =>
    change Commute (image (augmented G).relations
      (CompilerFrontend.substitute replacement p+CompilerFrontend.substitute replacement q)) _
    rw [image_add]
    exact hp.add_left hq
  | mul p q hp hq =>
    change Commute (image (augmented G).relations
      (CompilerFrontend.substitute replacement p*CompilerFrontend.substitute replacement q)) _
    rw [image_mul]
    exact hp.mul_left hq
  | adj p hp => exact adjoint_commute G _ v hp

variable {ι : Type*} [Fintype ι]

def sourceEmbedding (P : Presentation ι) (j : ι × Fin 2) : Poly (Fin (realize P).numVars) :=
  .var (label P (source P j))

def sourceDecoder (P : Presentation ι) (k : ι) : Poly (Fin (realize P).numVars) :=
  CompilerFrontend.substitute (sourceEmbedding P) (CompilerFrontend.replacement P k)

def decodedRelation (P : Presentation ι) (r : Fin P.relations.length) : Poly (Fin (realize P).numVars) :=
  CompilerFrontend.substitute (sourceDecoder P) (P.relations.get r)

theorem embedded_source_commute (P : Presentation ι) (r : Fin P.relations.length)
    (p : Poly (ι × Fin 2)) (i : Fin (q P r)) :
    Commute (image (augmented (game (tables P))).relations
      (CompilerFrontend.substitute (sourceEmbedding P) p)) (value (tables P) (Z P r i)) := by
  apply substituted_commute (game (tables P)) (label P (Z P r i)) (sourceEmbedding P)
  intro j
  exact source_Z_commute P r j i

/-- This is the complete source/Z primitive family, for the original domain
decoder and original source polynomial, rather than only its reflection letters. -/
theorem decoded_source_commute (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r)) :
    Commute (image (augmented (game (tables P))).relations (decodedRelation P r))
      (value (tables P) (Z P r i)) := by
  apply substituted_commute (game (tables P)) (label P (Z P r i)) (sourceDecoder P)
  intro k
  exact embedded_source_commute P r (CompilerFrontend.replacement P k) i

theorem source_commutator_certificate (P : Presentation ι) (r : Fin P.relations.length)
    (i : Fin (q P r)) :
    image (augmented (game (tables P))).relations
      (decodedRelation P r * .var (label P (Z P r i))-
        .var (label P (Z P r i))*decodedRelation P r)=0 := by
  simp only [image_sub,image_mul]
  exact sub_eq_zero.mpr (decoded_source_commute P r i).eq

def selectorPolynomial (P : Presentation ι) (r : Fin P.relations.length) : Poly (Fin (realize P).numVars) :=
  CompilerMultiSelector.polyOrdered (fun i => CompilerMultiSelector.polyAtom (.var (label P (X P r i))) true)

def unnormalizedCornerResidual (P : Presentation ι) (r : Fin P.relations.length) :
    Poly (Fin (realize P).numVars) :=
  cornerPolynomial P r - selectorPolynomial P r *
    CompilerMultiSelector.polyOrdered (fun i => .var (label P (control P r i))) * selectorPolynomial P r

/-- A finite certificate for the AND/conjugacy corner substitution. This does
not yet identify E_pol S E_pol with the normalized original source polynomial. -/
theorem unnormalized_corner_certificate (P : Presentation ι) (r : Fin P.relations.length) :
    image (augmented (realize P)).relations (unnormalizedCornerResidual P r)=0 := by
  simp only [unnormalizedCornerResidual,cornerPolynomial,selectorPolynomial,image_sub,image_mul,
    CompilerMultiSelector.image_atom,CompilerMultiSelector.image_ordered]
  change (CompilerMultiSelector.atom (value (tables P) (E P r)) true *
    CompilerMultiSelector.atom (value (tables P) (F P r)) true * wordValue P r)-
    ((CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true))*
      wordValue P r*(CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (value (tables P) (X P r i)) true)))=0
  exact sub_eq_zero.mpr (conjugate_corner_substitution P r)

theorem unnormalized_corner_weighted (P : Presentation ι) (r : Fin P.relations.length) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (η : ℝ)
      (m : Model (booleanPresentation (realize P)) d η), 0 ≤ η →
      weighted m.state (Poly.eval m.value (unnormalizedCornerResidual P r)) ≤ C*η :=
  original_weighted_bound _ _ (unnormalized_corner_certificate P r)

def normalization (P : Presentation ι) (r : Fin P.relations.length) : ℚ :=
  2 * (denominator (relationWords P r) : ℚ) / (2:ℚ)^(q P r)

/-- The precise remaining normalized corner residual. This is a polynomial
definition, not an assertion or an assumed theorem. -/
def normalizedCornerResidual (P : Presentation ι) (r : Fin P.relations.length) :
    Poly (Fin (realize P).numVars) :=
  cornerPolynomial P r - .const (normalization P r) *
    (decodedRelation P r * selectorPolynomial P r)

end
end E2.CompilerNetwork
