import E2.CompilerFrontend
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.Congruence.Basic

namespace E2.CompilerUniversal
noncomputable section
open E2.CompilerPolynomial
open scoped Matrix.Norms.L2Operator
variable {ι : Type*}

abbrev Evaluation (ι : Type*) := (d : ℕ) → (ι → Mat d) → Mat d

def evaluate (p : Poly ι) : Evaluation ι := fun _ x => Poly.eval x p

@[simp] theorem evaluate_add (p q : Poly ι) : evaluate (p+q)=evaluate p+evaluate q := rfl
@[simp] theorem evaluate_mul (p q : Poly ι) : evaluate (p*q)=evaluate p*evaluate q := rfl
@[simp] theorem evaluate_neg (p : Poly ι) : evaluate (-p) = -evaluate p := by
  funext d x
  exact Poly.eval_neg x p
@[simp] theorem evaluate_zero : evaluate (0:Poly ι)=0 := by
  funext d x
  exact Poly.eval_zero x
@[simp] theorem evaluate_one : evaluate (1:Poly ι)=1 := by
  funext d x
  exact Poly.eval_one x

/-- The ring of rational polynomial matrix-evaluation functions. This is an
actual ring, so exact algebraic proofs can be performed in its quotients. -/
def evaluationRing (ι : Type*) : Subring (Evaluation ι) where
  carrier := {f | ∃ p : Poly ι, evaluate p=f}
  zero_mem' := ⟨0,evaluate_zero⟩
  one_mem' := ⟨1,evaluate_one⟩
  add_mem' := by
    rintro a b ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨p+q,rfl⟩
  mul_mem' := by
    rintro a b ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨p*q,rfl⟩
  neg_mem' := by
    rintro a ⟨p,rfl⟩
    exact ⟨-p,evaluate_neg p⟩

def polynomial (p : Poly ι) : evaluationRing ι := ⟨evaluate p,p,rfl⟩

@[simp] theorem polynomial_add (p q : Poly ι) : polynomial (p+q)=polynomial p+polynomial q := rfl
@[simp] theorem polynomial_mul (p q : Poly ι) : polynomial (p*q)=polynomial p*polynomial q := rfl
@[simp] theorem polynomial_zero : polynomial (0:Poly ι)=0 := Subtype.ext evaluate_zero
@[simp] theorem polynomial_one : polynomial (1:Poly ι)=1 := Subtype.ext evaluate_one
@[simp] theorem polynomial_neg (p : Poly ι) : polynomial (-p) = -polynomial p := Subtype.ext (evaluate_neg p)

def certified (relations : List (Poly ι)) (f : evaluationRing ι) : Prop :=
  ∃ p : Poly ι, Nonempty (Derivation relations p) ∧ evaluate p=f.val

/-- The ideal consists of finite derivations, not arbitrary exact consequences.
Its closure proofs construct finite certificate trees on both multiplication sides. -/
def certificateIdeal (relations : List (Poly ι)) : TwoSidedIdeal (evaluationRing ι) :=
  TwoSidedIdeal.mk' {f | certified relations f}
    (by exact ⟨0,⟨Derivation.zero⟩,evaluate_zero⟩)
    (by
      rintro a b ⟨p,⟨D⟩,hp⟩ ⟨q,⟨E⟩,hq⟩
      exact ⟨p+q,⟨D.add E⟩,by simp only [evaluate_add,hp,hq]; rfl⟩)
    (by
      rintro a ⟨p,⟨D⟩,hp⟩
      have dn : Derivation relations (-p) := (D.scale (-1)).equal (by
        intro d x
        simp only [Poly.eval_const,Poly.eval_mul,Poly.eval_neg]
        simp)
      exact ⟨-p,⟨dn⟩,by simp only [evaluate_neg,hp]; rfl⟩)
    (by
      rintro a b ⟨p,⟨D⟩,hp⟩
      obtain ⟨q,hq⟩ := a.property
      exact ⟨q*p,⟨D.left q⟩,by simp only [evaluate_mul,hp,hq]; rfl⟩)
    (by
      rintro a b ⟨p,⟨D⟩,hp⟩
      obtain ⟨q,hq⟩ := b.property
      exact ⟨p*q,⟨D.right q⟩,by simp only [evaluate_mul,hp,hq]; rfl⟩)

theorem mem_certificateIdeal (relations : List (Poly ι)) (f : evaluationRing ι) :
    f ∈ certificateIdeal relations ↔ certified relations f := by
  apply TwoSidedIdeal.mem_mk'

abbrev CertificateQuotient (relations : List (Poly ι)) := (certificateIdeal relations).ringCon.Quotient

def image (relations : List (Poly ι)) (p : Poly ι) : CertificateQuotient relations :=
  (certificateIdeal relations).ringCon.mk' (polynomial p)

@[simp] theorem image_add (relations : List (Poly ι)) (p q : Poly ι) :
    image relations (p+q)=image relations p+image relations q := by
  exact map_add (certificateIdeal relations).ringCon.mk' (polynomial p) (polynomial q)
@[simp] theorem image_mul (relations : List (Poly ι)) (p q : Poly ι) :
    image relations (p*q)=image relations p*image relations q := by
  exact map_mul (certificateIdeal relations).ringCon.mk' (polynomial p) (polynomial q)
@[simp] theorem image_one (relations : List (Poly ι)) : image relations (1:Poly ι)=1 := by
  simp [image]
@[simp] theorem image_zero (relations : List (Poly ι)) : image relations (0:Poly ι)=0 := by
  simp [image]

def scalarMap : ℚ →+* evaluationRing ι where
  toFun q := polynomial (.const q)
  map_zero' := polynomial_zero
  map_one' := polynomial_one
  map_add' q r := by
    apply Subtype.ext
    funext d x
    simp [polynomial,evaluate,Poly.eval,add_smul]
  map_mul' q r := by
    apply Subtype.ext
    funext d x
    simp [polynomial,evaluate,Poly.eval,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm (q:ℂ) (r:ℂ)]

theorem scalar_commute (q : ℚ) (f : evaluationRing ι) : Commute (scalarMap q) f := by
  change scalarMap q*f=f*scalarMap q
  apply Subtype.ext
  funext d x
  change ((q:ℂ) • (1:Mat d))*f.val d x=f.val d x*((q:ℂ) • (1:Mat d))
  simp only [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one]

instance evaluationAlgebra : Algebra ℚ (evaluationRing ι) :=
  scalarMap.toAlgebra' (fun q f => (scalar_commute q f).eq)

def quotientScalar (relations : List (Poly ι)) : ℚ →+* CertificateQuotient relations :=
  (certificateIdeal relations).ringCon.mk'.comp scalarMap

@[simp] theorem image_const (relations : List (Poly ι)) (q : ℚ) :
    image relations (.const q)=algebraMap ℚ (CertificateQuotient relations) q := rfl

theorem image_scale (relations : List (Poly ι)) (q : ℚ) (p : Poly ι) :
    image relations (.const q*p)=q • image relations p := by
  rw [image_mul,image_const,Algebra.smul_def]

@[simp] theorem image_neg (relations : List (Poly ι)) (p : Poly ι) :
    image relations (-p) = -image relations p := by
  simp [image]

@[simp] theorem image_sub (relations : List (Poly ι)) (p q : Poly ι) :
    image relations (p-q)=image relations p-image relations q := by
  change image relations (p+(-q))=_
  simp only [image_add,image_neg,sub_eq_add_neg]

/-- A zero equality in the certificate quotient extracts an actual finite
certificate. This justifies quantitative use of an exact quotient-ring proof. -/
theorem image_eq_zero_iff (relations : List (Poly ι)) (p : Poly ι) :
    image relations p=0 ↔ Nonempty (Derivation relations p) := by
  change (certificateIdeal relations).ringCon.mk' (polynomial p)=0 ↔ _
  rw [← TwoSidedIdeal.mem_ker,TwoSidedIdeal.ker_ringCon_mk',mem_certificateIdeal]
  constructor
  · rintro ⟨q,⟨D⟩,he⟩
    refine ⟨D.equal ?_⟩
    intro d x
    exact congrFun (congrFun he d) x
  · intro h
    exact ⟨p,h,rfl⟩

theorem image_relation (relations : List (Poly ι)) (p : Poly ι) (hp : p ∈ relations) :
    image relations p=0 :=
  (image_eq_zero_iff relations p).mpr ⟨Derivation.base p hp⟩

/-- The quotient certificate yields a dimension-independent linear weighted
bound on the supplied state, including every right-factor commutator cost. -/
theorem uniform_weighted_bound (relations : List (Poly ι)) (p : Poly ι)
    (hp : image relations p=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ (d : ℕ) (s : State d) (_hd : 0<d)
      (x : ι → Mat d) (η : ℝ), 0≤η →
      (∀ i, ‖x i‖≤1) → (∀ i, hs (comm (x i) s.xi)≤η) →
      (∀ r ∈ relations, weighted s (Poly.eval x r)≤η) →
      weighted s (Poly.eval x p)≤C*η := by
  obtain ⟨D⟩ := (image_eq_zero_iff relations p).mp hp
  exact ⟨D.cost,D.cost_nonneg,fun _ s hd x η hη hx hc hr => D.weighted_bound s hd x η hη hx hc hr⟩

/-- Simultaneous source-model reconstruction from the actual finite family of
quotient certificates. The dimension and supplied state are retained exactly.
No certificate-existence claim is included in this assembly theorem. -/
theorem reconstruct_from_certificates {κ : Type*} [Fintype κ]
    (P : Presentation κ) (Q : Presentation ι)
    (hQ : ∀ i, Q.domain i=Domain.reflection)
    (decoder : κ → Poly ι)
    (hdomains : ∀ (d : ℕ) (x : ι → Mat d),
      (∀ i, Domain.reflection.Holds (x i)) →
      ∀ k, (P.domain k).Holds (Poly.eval x (decoder k)))
    (hcert : ∀ r ∈ P.relations,
      image Q.relations (CompilerFrontend.substitute decoder r)=0) :
    ∃ C : ℝ, 0<C ∧ ∀ (η : ℝ) (d : ℕ) (m : Model Q d η), 0≤η →
      ∃ out : Model P d (C*η), out.state=m.state := by
  classical
  let D (j : Fin P.relations.length) :
      Derivation Q.relations (CompilerFrontend.substitute decoder (P.relations.get j)) :=
    Classical.choice ((image_eq_zero_iff _ _).mp (hcert _ (List.get_mem _ _)))
  let C : ℝ := 1 + (∑ j, (D j).cost) + ∑ k, commBudget (decoder k)
  have hcost : 0 ≤ ∑ j, (D j).cost := Finset.sum_nonneg (fun j _ => (D j).cost_nonneg)
  have hcomm : 0 ≤ ∑ k, commBudget (decoder k) :=
    Finset.sum_nonneg (fun k _ => commBudget_nonneg _)
  have hC : 0<C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro η d m hη
  have hx (i : ι) : Domain.reflection.Holds (m.value i) := by
    simpa only [hQ] using m.domains i
  have hn (i : ι) : ‖m.value i‖≤1 := CompilerFrontend.reflection_norm m.positive_dimension _ (hx i)
  let out : Model P d (C*η) := {
    positive_dimension := m.positive_dimension
    state := m.state
    value := fun k => Poly.eval m.value (decoder k)
    domains := hdomains d m.value hx
    defects := by
      intro r hr
      obtain ⟨j,hj⟩ := List.mem_iff_get.mp hr
      have hb := (D j).weighted_bound m.state m.positive_dimension m.value η hη hn
        m.state_commutators m.defects
      have hjC : (D j).cost ≤ C := by
        have h := Finset.single_le_sum (fun k _ => (D k).cost_nonneg) (Finset.mem_univ j)
        dsimp [C]
        linarith
      have hb' : weighted m.state (Poly.eval (fun k => Poly.eval m.value (decoder k)) r) ≤
          (D j).cost*η := by
        simpa only [CompilerFrontend.eval_substitute,hj] using hb
      exact hb'.trans (mul_le_mul_of_nonneg_right hjC hη)
    state_commutators := by
      intro k
      have hb := eval_comm_bound m.state m.positive_dimension m.value η hη hn
        m.state_commutators (decoder k)
      have hkC : commBudget (decoder k)≤C := by
        have h := Finset.single_le_sum (fun k _ => commBudget_nonneg (decoder k))
          (Finset.mem_univ k)
        dsimp [C]
        linarith
      exact hb.trans (mul_le_mul_of_nonneg_right hkC hη) }
  exact ⟨out,rfl⟩

/-- The original domain decoder is used, rather than a weakened source model.
Only the finite quotient certificates remain to be supplied by the compiled
context construction. -/
theorem source_reconstruction_from_certificates {κ : Type*} [Fintype κ]
    (P : Presentation κ) (Q : Presentation ι)
    (hQ : ∀ i, Q.domain i=Domain.reflection) (source : κ × Fin 2 → ι)
    (hcert : ∀ r ∈ P.relations,
      image Q.relations (CompilerFrontend.substitute
        (fun k => CompilerFrontend.substitute (fun j => Poly.var (source j))
          (CompilerFrontend.replacement P k)) r)=0) :
    ∃ C : ℝ, 0<C ∧ ∀ (η : ℝ) (d : ℕ) (m : Model Q d η), 0≤η →
      ∃ out : Model P d (C*η), out.state=m.state := by
  apply reconstruct_from_certificates P Q hQ _ _ hcert
  intro d x hx k
  simp only [CompilerFrontend.eval_substitute,Poly.eval_var]
  exact CompilerFrontend.replacement_domain P (fun j => x (source j)) (fun j => hx (source j)) k

end
end E2.CompilerUniversal

