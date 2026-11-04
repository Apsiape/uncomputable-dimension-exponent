import E2.CompilerDefinitions
import E2.CompilerGame
import E2.CompilerMultiSelector
import E2.CompilerControlled
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace E2.CompilerRealize
noncomputable section
open scoped BigOperators
open E2.CompilerPolynomial E2.CompilerUniversal

/-- The exact reflection domains are included explicitly in the certificate
ring. They are validated, with zero defect, against the original game model. -/
def augmented (G : BCSGame) : Presentation (Fin G.numVars) where
  domain _ := .reflection
  relations := (booleanPresentation G).relations ++
    (List.finRange G.numVars).map (fun v => Poly.var v * Poly.var v - 1) ++
    (List.finRange G.numVars).map (fun v => (Poly.var v).adj - Poly.var v)

def augmentModel (G : BCSGame) {d : ℕ} {η : ℝ}
    (m : Model (booleanPresentation G) d η) (hη : 0 ≤ η) : Model (augmented G) d η where
  positive_dimension := m.positive_dimension
  state := m.state
  value := m.value
  domains := m.domains
  state_commutators := m.state_commutators
  defects := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact m.defects r hr
      · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
        simpa [Poly.eval,(m.domains v).2] using hη
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
      simpa [Poly.eval,(m.domains v).1] using hη

abbrev AlgebraOf (G : BCSGame) := CertificateQuotient (augmented G).relations

def generator (G : BCSGame) (v : Fin G.numVars) : AlgebraOf G :=
  image (augmented G).relations (.var v)

theorem variable_square (G : BCSGame) (v : Fin G.numVars) :
    generator G v * generator G v = 1 := by
  have h := image_relation (augmented G).relations (.var v * .var v - 1)
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨v,by simp,rfl⟩)))
  simpa only [image_sub,image_mul,image_one,generator,sub_eq_zero] using h

theorem original_relation (G : BCSGame) (p : Poly (Fin G.numVars))
    (hp : p ∈ (booleanPresentation G).relations) : image (augmented G).relations p = 0 :=
  image_relation _ _ (List.mem_append_left _ (List.mem_append_left _ hp))

theorem variable_adjoint (G : BCSGame) (v : Fin G.numVars) :
    image (augmented G).relations (Poly.var v).adj=generator G v := by
  apply sub_eq_zero.mp
  have h := image_relation (augmented G).relations ((Poly.var v).adj-Poly.var v)
    (List.mem_append_right _ (List.mem_map.mpr ⟨v,by simp,rfl⟩))
  simpa only [image_sub,generator] using h

/-- Semantic equality steps are checked on arbitrary matrices, without
reflection or model assumptions. -/
theorem image_semantic {κ : Type*} (rs : List (Poly κ)) (p q : Poly κ)
    (h : ∀ (d : ℕ) (x : κ → Mat d), Poly.eval x p=Poly.eval x q) :
    image rs p=image rs q := by
  apply congrArg (certificateIdeal rs).ringCon.mk'
  apply Subtype.ext
  funext d x
  exact h d x

/-- Adjoint closure comes from the finite derivation constructor, while the
reflection domain identifies Z* with Z. -/
theorem adjoint_commute (G : BCSGame) (p : Poly (Fin G.numVars)) (v : Fin G.numVars)
    (hc : Commute (image (augmented G).relations p) (generator G v)) :
    Commute (image (augmented G).relations p.adj) (generator G v) := by
  have hz : image (augmented G).relations (p*Poly.var v-Poly.var v*p)=0 := by
    simp only [image_sub,image_mul]
    exact sub_eq_zero.mpr hc.eq
  obtain ⟨D⟩ := (image_eq_zero_iff _ _).mp hz
  have ha := (image_eq_zero_iff _ _).mpr ⟨D.adj⟩
  have he := image_semantic (augmented G).relations
    (p*Poly.var v-Poly.var v*p).adj
    ((Poly.var v).adj*p.adj-p.adj*(Poly.var v).adj) (by
      intro d x
      simp [Poly.eval_sub,Poly.eval,Matrix.conjTranspose_sub,Matrix.conjTranspose_mul])
  rw [he] at ha
  simp only [image_sub,image_mul,variable_adjoint] at ha
  exact (sub_eq_zero.mp ha).symm

theorem context_commute (G : BCSGame) (c : Fin G.contexts)
    (u v : Fin G.numVars) (hu : u ∈ G.scope c) (hv : v ∈ G.scope c) :
    Commute (generator G u) (generator G v) := by
  apply sub_eq_zero.mp
  have h : Poly.var u * Poly.var v - Poly.var v * Poly.var u ∈
      (booleanPresentation G).relations := by
    apply List.mem_flatMap.mpr
    refine ⟨c,by simp, List.mem_append_left _ ?_⟩
    simp only [commList,List.mem_flatMap,List.mem_map,Finset.mem_toList]
    exact ⟨.var u,⟨u,hu,rfl⟩,.var v,⟨v,hv,rfl⟩,rfl⟩
  simpa only [image_sub,image_mul,generator] using original_relation G _ h

def ports (G : BCSGame) (c : Fin G.contexts) :
    Fin (G.scope c).toList.length → Fin G.numVars := (G.scope c).toList.get

theorem ports_injective (G : BCSGame) (c : Fin G.contexts) :
    Function.Injective (ports G c) := (Finset.nodup_toList _).injective_get

theorem ports_mem (G : BCSGame) (c : Fin G.contexts)
    (i : Fin (G.scope c).toList.length) : ports G c i ∈ G.scope c :=
  Finset.mem_toList.mp (List.get_mem _ _)

def extendAssignment (G : BCSGame) (c : Fin G.contexts)
    (a : Fin (G.scope c).toList.length → Bool) : Fin G.numVars → Bool :=
  Function.extend (ports G c) a (fun _ => true)

@[simp] theorem extendAssignment_port (G : BCSGame) (c : Fin G.contexts)
    (a : Fin (G.scope c).toList.length → Bool) (i : Fin (G.scope c).toList.length) :
    extendAssignment G c a (ports G c i) = a i :=
  (ports_injective G c).extend_apply _ _ _

def joint {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}
    (x : Fin n → A) (a : Fin n → Bool) : A :=
  E2.CompilerBoolean.ordered (fun i => CompilerMultiSelector.atom (x i) (a i))

theorem image_assignment (G : BCSGame) (c : Fin G.contexts)
    (a : Fin G.numVars → Bool) :
    image (augmented G).relations (assignmentPolynomial G c a) =
      joint (fun i => generator G (ports G c i)) (fun i => a (ports G c i)) := by
  change image _ (CompilerMultiSelector.polyProduct _) = _
  rw [CompilerMultiSelector.image_product]
  unfold joint E2.CompilerBoolean.ordered
  conv_lhs => rw [← List.ofFn_get (G.scope c).toList]
  simp only [List.map_ofFn]
  congr 2
  funext i
  cases h : a (ports G c i) <;> dsimp [ports] at h <;>
    simp [image_mul,image_add,image_const,generator,CompilerMultiSelector.atom,ports,h,
      Algebra.smul_def,sub_eq_add_neg]

theorem forbidden_joint (G : BCSGame) (c : Fin G.contexts)
    (a : Fin (G.scope c).toList.length → Bool)
    (ha : extendAssignment G c a ∉ G.allowed c) :
    joint (fun i => generator G (ports G c i)) a = 0 := by
  have h := original_relation G (assignmentPolynomial G c (extendAssignment G c a)) (by
    apply List.mem_flatMap.mpr
    refine ⟨c,by simp,List.mem_append_right _ ?_⟩
    apply List.mem_map.mpr
    exact ⟨extendAssignment G c a,Finset.mem_toList.mpr (by simp [ha]),rfl⟩)
  simpa only [image_assignment,extendAssignment_port] using h

section Interpolation
variable {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}

def sign (b : Bool) : ℚ := if b then 1 else -1

theorem atom_partition (x : A) :
    CompilerMultiSelector.atom x true + CompilerMultiSelector.atom x false = 1 := by
  simp only [CompilerMultiSelector.atom,↓reduceIte,Bool.false_eq_true]
  module

theorem joint_partition (x : Fin n → A) : ∑ a, joint x a = 1 := by
  unfold joint
  rw [E2.CompilerBoolean.assignment_expansion]
  simp only [atom_partition]
  simp [E2.CompilerBoolean.ordered]

theorem atom_eigen (x : A) (hx : x*x=1) (b : Bool) :
    x * CompilerMultiSelector.atom x b = (sign b) • CompilerMultiSelector.atom x b := by
  cases b <;> simp only [CompilerMultiSelector.atom,sign,↓reduceIte,Bool.false_eq_true,
    Algebra.mul_smul_comm,mul_add,mul_sub,mul_one,hx]
  all_goals module

theorem eigen_joint (x : Fin n → A) (hx : ∀ i, x i*x i=1)
    (hc : ∀ i j, Commute (x i) (x j)) (a : Fin n → Bool) (i : Fin n) :
    x i * joint x a = (sign (a i)) • joint x a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    unfold joint
    rw [E2.CompilerBoolean.ordered_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← mul_assoc,atom_eigen _ (hx 0),Algebra.smul_mul_assoc]
    · have hcomm : Commute (x j.succ) (CompilerMultiSelector.atom (x 0) (a 0)) := by
        cases a 0 <;> simp only [CompilerMultiSelector.atom,↓reduceIte,Bool.false_eq_true]
        · exact ((Commute.one_right _).sub_right (hc j.succ 0)).smul_right _
        · exact ((Commute.one_right _).add_right (hc j.succ 0)).smul_right _
      rw [← mul_assoc,hcomm.eq,mul_assoc]
      have he := ih (fun k => x k.succ) (fun k => hx k.succ)
        (fun j k => hc j.succ k.succ) (fun k => a k.succ) j
      change _ * (_ * joint _ _) = _
      rw [he,Algebra.mul_smul_comm]
      rfl

/-- Local expressions used in truth tables. Multiplication is interpreted in
its written order; commuting context variables justify Boolean interpolation. -/
inductive Term (n : ℕ)
  | const : ℚ → Term n
  | var : Fin n → Term n
  | add : Term n → Term n → Term n
  | mul : Term n → Term n → Term n

def Term.value (x : Fin n → A) : Term n → A
  | .const q => algebraMap ℚ A q
  | .var i => x i
  | .add p q => p.value x + q.value x
  | .mul p q => p.value x * q.value x

def Term.scalar (a : Fin n → Bool) : Term n → ℚ
  | .const q => q
  | .var i => sign (a i)
  | .add p q => p.scalar a + q.scalar a
  | .mul p q => p.scalar a * q.scalar a

theorem Term.eigen (t : Term n) (x : Fin n → A) (hx : ∀ i, x i*x i=1)
    (hc : ∀ i j, Commute (x i) (x j)) (a : Fin n → Bool) :
    t.value x * joint x a = (t.scalar a) • joint x a := by
  induction t with
  | const q => exact (Algebra.smul_def _ _).symm
  | var i => exact eigen_joint x hx hc a i
  | add p q hp hq => simp only [Term.value,Term.scalar,add_mul,hp,hq,add_smul]
  | mul p q hp hq =>
    simp only [Term.value,Term.scalar,mul_assoc,hq,Algebra.mul_smul_comm,hp,smul_smul]
    rw [mul_comm]

theorem Term.interpolate (t : Term n) (x : Fin n → A) (hx : ∀ i, x i*x i=1)
    (hc : ∀ i j, Commute (x i) (x j)) :
    t.value x = ∑ a, (t.scalar a) • joint x a := by
  simp_rw [← t.eigen x hx hc]
  rw [← Finset.mul_sum,joint_partition,mul_one]

end Interpolation

def Term.poly {n : ℕ} {κ : Type*} (v : Fin n → κ) : Term n → Poly κ
  | .const q => .const q
  | .var i => .var (v i)
  | .add p q => p.poly v + q.poly v
  | .mul p q => p.poly v * q.poly v

@[simp] theorem Term.image {n : ℕ} (G : BCSGame) (v : Fin n → Fin G.numVars) (t : Term n) :
    image (augmented G).relations (t.poly v) = t.value (generator G ∘ v) := by
  induction t <;> simp_all [Term.poly,Term.value,generator,Function.comp_def]

/-- Truth-table extraction from the original Boolean game's actual sorted
scope. The extra ideal generators are its exact reflection-domain identities. -/
theorem table_certificate (G : BCSGame) (c : Fin G.contexts)
    (t : Term (G.scope c).toList.length)
    (hzero : ∀ a, extendAssignment G c a ∈ G.allowed c → t.scalar a = 0) :
    image (augmented G).relations (t.poly (ports G c)) = 0 := by
  rw [Term.image]
  change t.value (fun i => generator G (ports G c i))=0
  rw [Term.interpolate t _ (fun i => variable_square G _) (fun i j =>
    context_commute G c _ _ (ports_mem G c i) (ports_mem G c j))]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : extendAssignment G c a ∈ G.allowed c
  · rw [hzero a h,zero_smul]
  · rw [forbidden_joint G c a h,smul_zero]

/-- The eigenvalue argument needs only the displayed eigenrelations. -/
theorem Term.eigen_from {A : Type*} [Ring A] [Algebra ℚ A] {n : ℕ}
    (t : Term n) (x : Fin n → A) (a : Fin n → Bool) (J : A)
    (he : ∀ i, x i*J=sign (a i) • J) : t.value x*J=t.scalar a • J := by
  induction t with
  | const q => exact (Algebra.smul_def _ _).symm
  | var i => exact he i
  | add p q hp hq => simp only [Term.value,Term.scalar,add_mul,hp,hq,add_smul]
  | mul p q hp hq =>
    simp only [Term.value,Term.scalar,mul_assoc,hq,Algebra.mul_smul_comm,hp,smul_smul]
    rw [mul_comm]

theorem scope_eigen (G : BCSGame) (c : Fin G.contexts)
    (a : Fin (G.scope c).toList.length → Bool) (v : Fin G.numVars) (hv : v ∈ G.scope c) :
    generator G v * joint (fun i => generator G (ports G c i)) a =
      sign (extendAssignment G c a v) • joint (fun i => generator G (ports G c i)) a := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hv)
  change ports G c i=v at hi
  subst v
  rw [extendAssignment_port]
  exact eigen_joint _ (fun i => variable_square G _) (fun i j =>
    context_commute G c _ _ (ports_mem G c i) (ports_mem G c j)) a i

/-- Ports can be repeated and presented in any order. The ambient game's
sorted scope is used for the interpolation, and all locality is explicit. -/
theorem mapped_table_value (G : BCSGame) (c : Fin G.contexts) {n : ℕ}
    (v : Fin n → Fin G.numVars) (hv : ∀ i, v i ∈ G.scope c) (t : Term n)
    (hz : ∀ a ∈ G.allowed c, t.scalar (a ∘ v)=0) :
    t.value (generator G ∘ v)=0 := by
  have he (a : Fin (G.scope c).toList.length → Bool) :=
    t.eigen_from (generator G ∘ v) (extendAssignment G c a ∘ v)
      (joint (fun i => generator G (ports G c i)) a)
      (fun i => scope_eigen G c a (v i) (hv i))
  have hb : t.value (generator G ∘ v)=
      ∑ a, t.scalar (extendAssignment G c a ∘ v) •
        joint (fun i => generator G (ports G c i)) a := by
    simp_rw [← he]
    rw [← Finset.mul_sum,joint_partition,mul_one]
  rw [hb]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : extendAssignment G c a ∈ G.allowed c
  · rw [hz _ h,zero_smul]
  · rw [forbidden_joint G c a h,smul_zero]

/-- A certificate in this ring yields a same-state bound for an original
Boolean model: no additional relation is assumed of that model. -/
theorem original_weighted_bound (G : BCSGame) (p : Poly (Fin G.numVars))
    (hp : image (augmented G).relations p = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : ℕ) (η : ℝ)
      (m : Model (booleanPresentation G) d η), 0 ≤ η →
      weighted m.state (Poly.eval m.value p) ≤ C*η := by
  obtain ⟨C,hC,h⟩ := uniform_weighted_bound _ _ hp
  refine ⟨C,hC,?_⟩
  intro d η m hη
  let m' := augmentModel G m hη
  exact h d m.state m.positive_dimension m.value η hη
    (fun i => CompilerFrontend.reflection_norm m.positive_dimension _ (m.domains i))
    m.state_commutators m'.defects

end
end E2.CompilerRealize
