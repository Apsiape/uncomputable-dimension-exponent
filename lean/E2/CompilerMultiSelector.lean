import E2.CompilerUniversal
import E2.CompilerSelector

namespace E2.CompilerMultiSelector
noncomputable section
open scoped BigOperators
open E2.CompilerBoolean

variable {A : Type*} [Ring A] {n : ℕ}

theorem commute_ordered (a : A) (f : Fin n → A) (h : ∀ i, Commute a (f i)) :
    Commute a (ordered f) := by
  apply Commute.list_prod_right
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  exact h i

/-- Shuffle two ordered products. The factors at equal coordinates need not
commute; only distinct coordinates are interchanged. -/
theorem ordered_mul (f g : Fin n → A)
    (h : ∀ i j, i ≠ j → Commute (f i) (g j)) :
    ordered f*ordered g=ordered (fun i => f i*g i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ordered_succ,ordered_succ,ordered_succ]
    have hc : Commute (g 0) (ordered (fun i : Fin n => f i.succ)) := by
      apply commute_ordered
      intro i
      exact (h i.succ 0 (Fin.succ_ne_zero i)).symm
    calc
      _ = (f 0*g 0)*(ordered (fun i : Fin n => f i.succ)*ordered (fun i : Fin n => g i.succ)) := by
        rw [mul_assoc,← mul_assoc (ordered (fun i : Fin n => f i.succ)),← hc.eq]
        simp only [mul_assoc]
      _ = _ := by
        rw [ih (fun i => f i.succ) (fun i => g i.succ) (fun i j hij => h i.succ j.succ (by simpa using hij))]

theorem ordered_smul {R : Type*} [CommSemiring R] [Algebra R A]
    (k : R) (f : Fin n → A) : ordered (fun i => k • f i)=k^n • ordered f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ordered_succ,ordered_succ,ih]
    simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,pow_succ',mul_comm k]

/-- The full multi-coordinate compression identity. It is a ring-algebra
identity and therefore can be used inside the certificate quotient. -/
theorem compression {R : Type*} [CommSemiring R] [Algebra R A]
    (P Q : Fin n → A) (k : R)
    (hPP : ∀ i j, i ≠ j → Commute (P i) (P j))
    (hPQ : ∀ i j, i ≠ j → Commute (P i) (Q j))
    (hlocal : ∀ i, P i*Q i*P i=k • P i) :
    ordered P*ordered Q*ordered P=k^n • ordered P := by
  rw [ordered_mul P Q hPQ]
  rw [ordered_mul (fun i => P i*Q i) P]
  · simp_rw [hlocal]
    exact ordered_smul k P
  · intro i j hij
    exact (hPP i j hij).mul_left (hPQ j i (Ne.symm hij)).symm

/-- Both forward and reverse words are kept. No commutation between different
translation operators is needed for this stronger twirl formula. -/
def translate (Z : Fin n → A) (a : Fin n → Bool) : A :=
  ordered (fun i => if a i then Z i else 1)

def reverseTranslate (Z : Fin n → A) (a : Fin n → Bool) : A :=
  ((List.ofFn (fun i => if a i then Z i else 1)).reverse).prod

@[simp] theorem translate_succ (Z : Fin (n+1) → A) (b : Bool) (a : Fin n → Bool) :
    translate Z (Fin.cons b a)=(if b then Z 0 else 1)*translate (fun i => Z i.succ) a := by
  simp [translate,ordered]

@[simp] theorem reverseTranslate_succ (Z : Fin (n+1) → A) (b : Bool) (a : Fin n → Bool) :
    reverseTranslate Z (Fin.cons b a)=reverseTranslate (fun i => Z i.succ) a*(if b then Z 0 else 1) := by
  simp [reverseTranslate,List.ofFn_succ]

/-- The sum uses every one of the 2^n translates, including n=0. -/
theorem twirl (P Z : Fin n → A)
    (hcross : ∀ i j, i ≠ j → Commute (P i) (Z j))
    (hlocal : ∀ i, P i+Z i*P i*Z i=1) :
    (∑ a : Fin n → Bool, translate Z a*ordered P*reverseTranslate Z a)=1 := by
  induction n with
  | zero => simp [translate,reverseTranslate,ordered]
  | succ n ih =>
    rw [sum_assignments_succ]
    simp only [translate_succ,reverseTranslate_succ,ordered_succ]
    have ht (a : Fin n → Bool) :
        Commute (P 0) (translate (fun i : Fin n => Z i.succ) a) := by
      apply commute_ordered
      intro j
      split_ifs
      · exact hcross 0 j.succ (Ne.symm (Fin.succ_ne_zero j))
      · exact Commute.one_right _
    have he (b : Bool) (a : Fin n → Bool) :
        ((if b then Z 0 else 1)*translate (fun i : Fin n => Z i.succ) a)*
          (P 0*ordered (fun i : Fin n => P i.succ))*
          (reverseTranslate (fun i : Fin n => Z i.succ) a*(if b then Z 0 else 1)) =
        (if b then Z 0 else 1)*P 0*
          (translate (fun i : Fin n => Z i.succ) a*ordered (fun i : Fin n => P i.succ)*
            reverseTranslate (fun i : Fin n => Z i.succ) a)*(if b then Z 0 else 1) := by
      calc
        _ = (if b then Z 0 else 1)*
            (translate (fun i : Fin n => Z i.succ) a*P 0)*
            ordered (fun i : Fin n => P i.succ)*
            reverseTranslate (fun i : Fin n => Z i.succ) a*(if b then Z 0 else 1) := by
          simp only [mul_assoc]
        _ = _ := by rw [← (ht a).eq]; simp only [mul_assoc]
    simp_rw [he,← Finset.sum_mul,← Finset.mul_sum]
    rw [ih (fun i => P i.succ) (fun i => Z i.succ) (fun i j hij => hcross i.succ j.succ (by simpa using hij)) (fun i => hlocal i.succ)]
    simpa [Fintype.sum_bool,add_comm] using hlocal 0

/-- Translation of every corner reconstructs the original polynomial. All
source/translation commutations remain explicit hypotheses. -/
theorem split (P Z : Fin n → A) (Q p k : A)
    (hcorner : Q=k*p*ordered P)
    (hcomm : ∀ i, Commute p (Z i))
    (hk : ∀ i, Commute k (Z i))
    (htwirl : (∑ a : Fin n → Bool, translate Z a*ordered P*reverseTranslate Z a)=1) :
    (∑ a : Fin n → Bool, translate Z a*Q*reverseTranslate Z a)=k*p := by
  have hc (a : Fin n → Bool) : Commute (k*p) (translate Z a) := by
    apply commute_ordered
    intro i
    split_ifs
    · exact (hk i).mul_left (hcomm i)
    · exact Commute.one_right _
  have he (a : Fin n → Bool) : translate Z a*Q*reverseTranslate Z a=
      (k*p)*(translate Z a*ordered P*reverseTranslate Z a) := by
    rw [hcorner]
    calc
      _ = (translate Z a*(k*p))*ordered P*reverseTranslate Z a := by simp only [mul_assoc]
      _ = _ := by rw [← (hc a).eq]; simp only [mul_assoc]
  simp_rw [he]
  rw [← Finset.mul_sum,htwirl,mul_one]

section Pauli
variable [Algebra ℚ A]

def atom (X : A) (b : Bool) : A :=
  if b then (1/2 : ℚ) • (1+X) else (1/2 : ℚ) • (1-X)

theorem atom_projection (X : A) (hX : X*X=1) : atom X true*atom X true=atom X true := by
  have he : (1+X)*(1+X)=(2:ℚ) • (1+X) := by
    simp only [add_mul,mul_add,one_mul,mul_one,hX]
    module
  simp only [atom,↓reduceIte,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
  rw [he,smul_smul]
  norm_num

theorem atom_commute (X Y : A) (h : Commute X Y) (a b : Bool) :
    Commute (atom X a) (atom Y b) := by
  cases a <;> cases b <;> dsimp only [atom] <;>
    apply Commute.smul_left <;> apply Commute.smul_right
  · exact (Commute.one_right _).sub_right ((Commute.one_left Y).sub_left h)
  · exact (Commute.one_right _).add_right ((Commute.one_left Y).sub_left h)
  · exact (Commute.one_right _).sub_right ((Commute.one_left Y).add_left h)
  · exact (Commute.one_right _).add_right ((Commute.one_left Y).add_left h)

theorem pauli_compression (X Z : A) (hX : X*X=1) (hanti : X*Z+Z*X=0) (b : Bool) :
    atom X true*atom Z b*atom X true=(1/2:ℚ) • atom X true := by
  have hzero : atom X true*Z*atom X true=0 := by
    have he := E2.CompilerSelector.pauli_compression_certificate X Z
    rw [hX,hanti] at he
    simp only [add_zero,mul_zero,zero_mul,sub_self] at he
    simp only [atom,↓reduceIte,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,he,smul_zero]
  have hp := atom_projection X hX
  cases b <;> simp only [atom,↓reduceIte]
  · change atom X true*((1/2:ℚ) • (1-Z))*atom X true=_
    rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    congr 1
    rw [mul_sub,mul_one,sub_mul,hp,hzero,sub_zero]
    rfl
  · change atom X true*((1/2:ℚ) • (1+Z))*atom X true=_
    rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
    congr 1
    rw [mul_add,mul_one,add_mul,hp,hzero,add_zero]
    rfl

theorem pauli_twirl (X Z : A) (hZ : Z*Z=1) (hanti : X*Z+Z*X=0) :
    atom X true+Z*atom X true*Z=1 := by
  have he := E2.CompilerSelector.pauli_twirl_certificate X Z
  have hanti' : Z*X+X*Z=0 := by simpa [add_comm] using hanti
  rw [hZ,hanti'] at he
  simp only [sub_self,mul_zero,zero_mul,zero_add] at he
  have he' := sub_eq_zero.mp he
  simp only [atom,↓reduceIte,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,← smul_add]
  rw [he']
  module

/-- The paper's full 2^n-selector compression, for every joint Z assignment. -/
theorem pauli_multi_compression (X Z : Fin n → A)
    (hX : ∀ i, X i*X i=1)
    (hanti : ∀ i, X i*Z i+Z i*X i=0)
    (hXX : ∀ i j, i ≠ j → Commute (X i) (X j))
    (hXZ : ∀ i j, i ≠ j → Commute (X i) (Z j)) (a : Fin n → Bool) :
    ordered (fun i => atom (X i) true)*ordered (fun i => atom (Z i) (a i))*
      ordered (fun i => atom (X i) true) =
        ((1/2:ℚ)^n) • ordered (fun i => atom (X i) true) := by
  exact compression _ _ _
    (fun i j hij => atom_commute _ _ (hXX i j hij) _ _)
    (fun i j hij => atom_commute _ _ (hXZ i j hij) _ _)
    (fun i => pauli_compression _ _ (hX i) (hanti i) (a i))

/-- The full Pauli twirl. Distinct Z pairs need not commute when the reverse
word is retained on the right. -/
theorem pauli_multi_twirl (X Z : Fin n → A)
    (hZ : ∀ i, Z i*Z i=1)
    (hanti : ∀ i, X i*Z i+Z i*X i=0)
    (hXZ : ∀ i j, i ≠ j → Commute (X i) (Z j)) :
    (∑ a : Fin n → Bool, translate Z a*ordered (fun i => atom (X i) true)*reverseTranslate Z a)=1 := by
  apply twirl
  · intro i j hij
    exact ((Commute.one_left _).add_left (hXZ i j hij)).smul_left _
  · intro i
    exact pauli_twirl _ _ (hZ i) (hanti i)

/-- No selector corner can conceal a nonzero source polynomial once every
translate is included and the scalar normalization is nonzero. -/
theorem source_from_zero_corner (P Z : Fin n → A) (Q p : A) (k : ℚ)
    (hk : k ≠ 0) (hQ : Q=0) (hcorner : Q=k • (p*ordered P))
    (hcomm : ∀ i, Commute p (Z i))
    (htwirl : (∑ a : Fin n → Bool, translate Z a*ordered P*reverseTranslate Z a)=1) : p=0 := by
  have hc : Q=(algebraMap ℚ A k)*p*ordered P := by
    simpa only [Algebra.smul_def,mul_assoc] using hcorner
  have he := split P Z Q p (algebraMap ℚ A k) hc hcomm
    (fun i => Algebra.commutes k (Z i)) htwirl
  rw [hQ] at he
  simp only [mul_zero,zero_mul,Finset.sum_const_zero] at he
  have hz : k • p=0 := by simpa only [Algebra.smul_def] using he.symm
  have hinv := congrArg (fun x : A => k⁻¹ • x) hz
  simpa only [smul_smul,inv_mul_cancel₀ hk,one_smul,smul_zero] using hinv

end Pauli

section ControlledWords
variable {α : Type*} [Fintype α] [DecidableEq α]

def blockSum (e W : α → A) : A := ∑ i, e i*W i

def control (e a : A) : A := 1-e+e*a

theorem blockSum_mul (e W V : α → A)
    (hee : ∀ i j, e i*e j=if i=j then e i else 0)
    (hcomm : ∀ i j, Commute (W i) (e j)) :
    blockSum e W*blockSum e V=blockSum e (fun i => W i*V i) := by
  have ht (i j : α) : (e i*W i)*(e j*V j)=if i=j then e i*(W i*V i) else 0 := by
    calc
      _ = (e i*(W i*e j))*V j := by simp only [mul_assoc]
      _ = (e i*e j)*(W i*V j) := by rw [(hcomm i j).eq]; simp only [mul_assoc]
      _ = _ := by
        rw [hee]
        split_ifs with h
        · subst j; rfl
        · simp
  simp only [blockSum,Finset.sum_mul,Finset.mul_sum,ht]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem control_blockSum (e : α → A) (hsum : ∑ i, e i=1) (j : α) (a : A) :
    control (e j) a=blockSum e (fun i => if i=j then a else 1) := by
  symm
  calc
    _ = ∑ i, (e i + if i=j then e j*a-e j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=j
      · subst i; simp
      · simp [hi]
    _ = control (e j) a := by simp [Finset.sum_add_distrib,hsum,control]; abel

/-- Complete controlled-word routing, with arbitrary finite selector count and
arbitrary word length. Each selector receives exactly its own ordered letters.
This identity also routes signed constant factors and empty words. -/
theorem controlled_word_blocks (e : α → A)
    (hsum : ∑ i, e i=1)
    (hee : ∀ i j, e i*e j=if i=j then e i else 0)
    (letters : List (α × A))
    (hcomm : ∀ t ∈ letters, ∀ i, Commute t.2 (e i)) :
    (letters.map (fun t => control (e t.1) t.2)).prod =
      blockSum e (fun i => (letters.map (fun t => if i=t.1 then t.2 else 1)).prod) := by
  induction letters with
  | nil => simpa [blockSum] using hsum.symm
  | cons t letters ih =>
    have hhead := hcomm t (List.mem_cons_self)
    have htail : ∀ u ∈ letters, ∀ i, Commute u.2 (e i) :=
      fun u hu => hcomm u (List.mem_cons_of_mem t hu)
    simp only [List.map_cons,List.prod_cons]
    rw [ih htail,control_blockSum e hsum t.1 t.2,blockSum_mul e]
    · exact hee
    · intro i j
      split_ifs
      · exact hhead j
      · exact Commute.one_left _

end ControlledWords
section PolynomialCertificates
open E2.CompilerUniversal E2.CompilerPolynomial
variable {κ : Type*}

def polyProduct (ps : List (Poly κ)) : Poly κ := ps.foldr (· * ·) 1

def polyOrdered (f : Fin n → Poly κ) : Poly κ := polyProduct (List.ofFn f)

def polyAtom (X : Poly κ) (b : Bool) : Poly κ :=
  .const (1/2) * (if b then 1+X else 1-X)

def polyTranslate (Z : Fin n → Poly κ) (a : Fin n → Bool) : Poly κ :=
  polyOrdered (fun i => if a i then Z i else 1)

def polyReverseTranslate (Z : Fin n → Poly κ) (a : Fin n → Bool) : Poly κ :=
  polyProduct (List.ofFn (fun i => if a i then Z i else 1)).reverse

@[simp] theorem image_product (relations : List (Poly κ)) (ps : List (Poly κ)) :
    image relations (polyProduct ps)=(ps.map (image relations)).prod := by
  induction ps with
  | nil => simp [polyProduct]
  | cons p ps ih => simpa only [polyProduct,List.foldr_cons,image_mul,List.map_cons,List.prod_cons] using congrArg (image relations p*·) ih

@[simp] theorem image_ordered (relations : List (Poly κ)) (f : Fin n → Poly κ) :
    image relations (polyOrdered f)=ordered (fun i => image relations (f i)) := by
  simp only [polyOrdered,image_product,List.map_ofFn,ordered]
  rfl

@[simp] theorem image_atom (relations : List (Poly κ)) (X : Poly κ) (b : Bool) :
    image relations (polyAtom X b)=atom (image relations X) b := by
  cases b <;> simp only [polyAtom,Bool.false_eq_true,↓reduceIte,image_scale,image_sub,image_one,image_add,atom]

@[simp] theorem image_translate (relations : List (Poly κ)) (Z : Fin n → Poly κ) (a : Fin n → Bool) :
    image relations (polyTranslate Z a)=translate (fun i => image relations (Z i)) a := by
  simp [polyTranslate,translate,apply_ite]

@[simp] theorem image_reverseTranslate (relations : List (Poly κ)) (Z : Fin n → Poly κ) (a : Fin n → Bool) :
    image relations (polyReverseTranslate Z a)=reverseTranslate (fun i => image relations (Z i)) a := by
  simp only [polyReverseTranslate,image_product,List.map_reverse,List.map_ofFn,reverseTranslate]
  congr 2
  congr 1
  funext i
  split_ifs with h <;> simp [h]

/-- A finite certificate for the entire selector compression, extracted from
an exact proof in the certificate quotient. Primitive relation occurrences,
not exact matrix hypotheses, are the only inputs. -/
theorem compression_certificate (relations : List (Poly κ)) (X Z : Fin n → Poly κ)
    (hX : ∀ i, X i*X i-1 ∈ relations)
    (hanti : ∀ i, X i*Z i+Z i*X i ∈ relations)
    (hXX : ∀ i j, i ≠ j → X i*X j-X j*X i ∈ relations)
    (hXZ : ∀ i j, i ≠ j → X i*Z j-Z j*X i ∈ relations) (a : Fin n → Bool) :
    Nonempty (Derivation relations
      (polyOrdered (fun i => polyAtom (X i) true)*polyOrdered (fun i => polyAtom (Z i) (a i))*
        polyOrdered (fun i => polyAtom (X i) true)-
        .const ((1/2:ℚ)^n)*polyOrdered (fun i => polyAtom (X i) true))) := by
  apply (image_eq_zero_iff relations _).mp
  simp only [image_sub,image_mul,image_ordered,image_atom,image_const]
  apply sub_eq_zero.mpr
  rw [← Algebra.smul_def]
  apply pauli_multi_compression
  · intro i
    have h := image_relation relations _ (hX i)
    simpa only [image_sub,image_mul,image_one,sub_eq_zero] using h
  · intro i
    have h := image_relation relations _ (hanti i)
    simpa only [image_add,image_mul] using h
  · intro i j hij
    have h := image_relation relations _ (hXX i j hij)
    exact sub_eq_zero.mp (by simpa only [image_sub,image_mul] using h)
  · intro i j hij
    have h := image_relation relations _ (hXZ i j hij)
    exact sub_eq_zero.mp (by simpa only [image_sub,image_mul] using h)

def polySum (ps : List (Poly κ)) : Poly κ := ps.foldr (· + ·) 0

@[simp] theorem image_sum (relations : List (Poly κ)) (ps : List (Poly κ)) :
    image relations (polySum ps)=(ps.map (image relations)).sum := by
  induction ps with
  | nil => simp [polySum]
  | cons p ps ih => simpa only [polySum,List.foldr_cons,image_add,List.map_cons,List.sum_cons] using congrArg (image relations p+·) ih

def polyTwirl (X Z : Fin n → Poly κ) : Poly κ :=
  polySum (Finset.univ.toList.map (fun a : Fin n → Bool =>
    polyTranslate Z a*polyOrdered (fun i => polyAtom (X i) true)*polyReverseTranslate Z a))-1

/-- Every translated Pauli corner is included in this finite certificate. -/
theorem twirl_certificate (relations : List (Poly κ)) (X Z : Fin n → Poly κ)
    (hZ : ∀ i, Z i*Z i-1 ∈ relations)
    (hanti : ∀ i, X i*Z i+Z i*X i ∈ relations)
    (hXZ : ∀ i j, i ≠ j → X i*Z j-Z j*X i ∈ relations) :
    Nonempty (Derivation relations (polyTwirl X Z)) := by
  apply (image_eq_zero_iff relations _).mp
  simp only [polyTwirl,image_sub,image_sum,List.map_map,Function.comp_apply,image_mul,
    image_translate,image_ordered,image_atom,image_reverseTranslate,image_one,Finset.sum_map_toList]
  apply sub_eq_zero.mpr
  apply pauli_multi_twirl
  · intro i
    have h := image_relation relations _ (hZ i)
    simpa only [image_sub,image_mul,image_one,sub_eq_zero] using h
  · intro i
    have h := image_relation relations _ (hanti i)
    simpa only [image_add,image_mul] using h
  · intro i j hij
    have h := image_relation relations _ (hXZ i j hij)
    exact sub_eq_zero.mp (by simpa only [image_sub,image_mul] using h)

/-- Full source-equation certificate from the selector network's primitive
relations. The Boolean-context construction must still derive these primitives;
this theorem does not assume that it has done so. -/
theorem source_certificate (relations : List (Poly κ)) (X Z : Fin n → Poly κ)
    (Q p : Poly κ) (k : ℚ) (hk : k ≠ 0)
    (hZ : ∀ i, Z i*Z i-1 ∈ relations)
    (hanti : ∀ i, X i*Z i+Z i*X i ∈ relations)
    (hXZ : ∀ i j, i ≠ j → X i*Z j-Z j*X i ∈ relations)
    (hQ : Q ∈ relations)
    (hcorner : Q-.const k*(p*polyOrdered (fun i => polyAtom (X i) true)) ∈ relations)
    (hcomm : ∀ i, p*Z i-Z i*p ∈ relations) :
    Nonempty (Derivation relations p) := by
  apply (image_eq_zero_iff relations p).mp
  apply source_from_zero_corner (fun i => atom (image relations (X i)) true)
    (fun i => image relations (Z i)) (image relations Q) (image relations p) k hk
  · exact image_relation relations Q hQ
  · have h := image_relation relations _ hcorner
    apply sub_eq_zero.mp
    simpa only [image_sub,image_scale,image_mul,image_ordered,image_atom,image_const,Algebra.smul_def] using h
  · intro i
    have h := image_relation relations _ (hcomm i)
    exact sub_eq_zero.mp (by simpa only [image_sub,image_mul] using h)
  · have h := (image_eq_zero_iff relations _).mpr (twirl_certificate relations X Z hZ hanti hXZ)
    simpa only [polyTwirl,image_sub,image_sum,List.map_map,Function.comp_apply,image_mul,
      image_translate,image_ordered,image_atom,image_reverseTranslate,image_one,
      Finset.sum_map_toList,sub_eq_zero] using h

end PolynomialCertificates

end
end E2.CompilerMultiSelector
