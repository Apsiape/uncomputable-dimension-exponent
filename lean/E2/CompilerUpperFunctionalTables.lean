import E2.CompilerUpperExactTables

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks
variable {V : Type*} [Fintype V] {d n : ℕ}
local instance : DecidableEq V := Classical.decEq V

/-- Distinct scalar eigenvalues force a joint outcome to vanish. -/
theorem scalar_eigen_zero (J : Mat d) (a b : ℚ)
    (h : (a:ℂ) • J=(b:ℂ) • J) (hne : a≠b) : J=0 := by
  have hz : ((a:ℂ)-(b:ℂ)) • J=0 := by rw [sub_smul,h,sub_self]
  apply (smul_eq_zero.mp hz).resolve_left
  exact_mod_cast sub_ne_zero.mpr hne

theorem sign_injective : Function.Injective E2.CompilerRealize.sign := by
  intro a b h
  cases a <;> cases b <;> first | rfl | norm_num [E2.CompilerRealize.sign] at h

/-- Evaluate an atomic projection on any simultaneous eigenspace. -/
theorem atom_eigen_on (x J : Mat d) (a b : Bool)
    (he : x*J=(E2.CompilerRealize.sign a:ℂ) • J) :
    E2.CompilerBoolean.atom x b*J=if b=a then J else 0 := by
  cases a <;> cases b <;>
    simp [E2.CompilerBoolean.atom,Algebra.smul_mul_assoc,add_mul,sub_mul,he,E2.CompilerRealize.sign] <;> module

/-- A full assignment projector selects exactly its simultaneous eigenlabel. -/
theorem joint_eigen_on (x : Fin n → Mat d) (a b : Fin n → Bool) (J : Mat d)
    (he : ∀ i, x i*J=(E2.CompilerRealize.sign (a i):ℂ) • J) :
    E2.CompilerBoolean.joint x b*J=if b=a then J else 0 := by
  classical
  induction n with
  | zero => simp [E2.CompilerBoolean.joint,E2.CompilerBoolean.ordered,Subsingleton.elim b a]
  | succ n ih =>
    simp only [E2.CompilerBoolean.joint,E2.CompilerBoolean.ordered_succ,mul_assoc]
    change E2.CompilerBoolean.atom (x 0) (b 0)*(E2.CompilerBoolean.joint (fun i => x i.succ) (fun i => b i.succ)*J)=_
    rw [ih _ _ _ (fun i => he i.succ)]
    by_cases ht : (fun i : Fin n => b i.succ)=(fun i : Fin n => a i.succ)
    · simp only [ht,↓reduceIte,atom_eigen_on _ _ _ _ (he 0)]
      have hh : b=a ↔ b 0=a 0 := by
        constructor
        · intro h; rw [h]
        · intro h; funext i; refine Fin.cases h (fun j => congrFun ht j) i
      simp only [hh]
    · have hn : b≠a := by intro h; apply ht; rw [h]
      simp [ht,hn]

/-- Negation tables have exact PVMs, with no assumption on distinct input labels beyond freshness. -/
theorem negation_measurement (v out : V) (fresh : out ∉ ({v}:Finset V)) (x : V → Mat d)
    (hx : ∀ w ∈ insert out ({v}:Finset V), Domain.reflection.Holds (x w))
    (ho : x out= -x v) :
    ∃ A : TableMeasurement (functional {v} out fresh (fun a => !(a v))
      (by intro a b h; rw [h v (by simp)])) d,
      ∀ w ∈ insert out ({v}:Finset V), A.marginal w=decodeProjection (x w) := by
  apply exact_table_measurement
  · exact hx
  · intro i hi j hj
    simp only [functional,Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact Commute.refl _
    · rw [ho]; exact (Commute.refl _).neg_left
    · rw [ho]; exact (Commute.refl _).neg_right
    · exact Commute.refl _
  · intro a J he hbad
    have h := he out (by simp [functional])
    rw [ho,neg_mul,he v (by simp [functional]),← neg_smul] at h
    apply scalar_eigen_zero J (-E2.CompilerRealize.sign (a v)) (E2.CompilerRealize.sign (a out)) (by simpa using h)
    intro hh
    apply hbad
    change a out= !(a v)
    cases hi : a v <;> cases hout : a out <;> first | rfl | norm_num [E2.CompilerRealize.sign,hi,hout] at hh

/-- AND is represented by the full true-input joint projector. -/
theorem and_measurement (out : V) (port : Fin n → V) (x : V → Mat d)
    (hx : ∀ i, Domain.reflection.Holds (x (port i)))
    (hc : ∀ i j, Commute (x (port i)) (x (port j)))
    (ho : x out=encodeProjection (E2.CompilerBoolean.joint (x ∘ port) (fun _ => true))) :
    ∃ A : TableMeasurement (andTable out (Finset.univ.image port)) d,
      ∀ v ∈ (andTable out (Finset.univ.image port)).scope, A.marginal v=decodeProjection (x v) := by
  classical
  have hout : Domain.reflection.Holds (x out) := by
    rw [ho]; exact encode_projection _ (joint_domain _ hx hc _)
  have hio (i) : Commute (x (port i)) (x out) := by
    rw [ho]
    exact ((commute_joint _ _ (hc i) _).smul_right (2:ℂ)).sub_right (Commute.one_right _)
  apply exact_table_measurement
  · intro v hv
    simp only [andTable,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hv
    rcases hv with rfl | ⟨i,rfl⟩
    · exact hout
    · exact hx i
  · intro v hv w hw
    simp only [andTable,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hv hw
    rcases hv with rfl | ⟨i,rfl⟩ <;> rcases hw with rfl | ⟨j,rfl⟩
    · exact Commute.refl _
    · exact (hio j).symm
    · exact hio i
    · exact hc i j
  · intro a J he hbad
    have h := he out (by simp [andTable])
    have hj := joint_eigen_on (x ∘ port) (a ∘ port) (fun _ => true) J
      (fun i => he (port i) (by simp [andTable]))
    rw [ho,encodeProjection,sub_mul,Algebra.smul_mul_assoc,hj,one_mul] at h
    have hp : (fun _ : Fin n => true)=a ∘ port ↔ ∀ v ∈ Finset.univ.image port, a v=true := by
      simp only [Finset.mem_image,Finset.mem_univ,true_and,forall_exists_index,forall_apply_eq_imp_iff,Function.comp_def]
      constructor
      · intro h i; exact (congrFun h i).symm
      · intro h; funext i; exact (h i).symm
    by_cases hg : (fun _ : Fin n => true)=a ∘ port
    · rw [if_pos hg] at h
      have he' : (1:ℂ) • J=(E2.CompilerRealize.sign (a out):ℂ) • J := by
        calc _ = (2:ℂ) • J-J := by module
             _ = _ := h
      apply scalar_eigen_zero J 1 (E2.CompilerRealize.sign (a out)) (by simpa using he')
      intro hh
      apply hbad
      change a out=true ↔ ∀ v ∈ Finset.univ.image port, a v=true
      have ha : a out=true := sign_injective (by simpa [E2.CompilerRealize.sign] using hh.symm)
      exact iff_of_true ha (hp.mp hg)
    · rw [if_neg hg] at h
      have he' : (-1:ℂ) • J=(E2.CompilerRealize.sign (a out):ℂ) • J := by simpa using h
      apply scalar_eigen_zero J (-1) (E2.CompilerRealize.sign (a out)) (by simpa using he')
      intro hh
      apply hbad
      change a out=true ↔ ∀ v ∈ Finset.univ.image port, a v=true
      have ha : a out=false := sign_injective (by simpa [E2.CompilerRealize.sign] using hh.symm)
      exact iff_of_false (by simp [ha]) (fun hh => hg (hp.mpr hh))

/-- The controlled Boolean truth table, evaluated on every input eigenspace. -/
theorem controlled_eigen_on (port : Fin n → V) (src : Option V) (positive : Bool)
    (selector : Fin n → Bool) (x : V → Mat d) (a : V → Bool) (J : Mat d)
    (hz : ∀ i, x (port i)*J=(E2.CompilerRealize.sign (a (port i)):ℂ) • J)
    (hs : ∀ v, src=some v → x v*J=(E2.CompilerRealize.sign (a v):ℂ) • J) :
    controlled (E2.CompilerBoolean.joint (x ∘ port) selector)
      (if positive then src.elim 1 x else -(src.elim 1 x))*J =
    (E2.CompilerRealize.sign
      (if ∀ i, a (port i)=selector i then
        if positive then src.elim true a else !(src.elim true a)
       else true):ℂ) • J := by
  classical
  have hj := joint_eigen_on (x ∘ port) (a ∘ port) selector J hz
  have hS : (if positive then src.elim 1 x else -(src.elim 1 x))*J=
      (E2.CompilerRealize.sign (if positive then src.elim true a else !(src.elim true a)):ℂ) • J := by
    cases hsrc : src with
    | none => cases positive <;> simp [hsrc,E2.CompilerRealize.sign]
    | some v =>
      have hv := hs v hsrc
      cases positive <;> cases hav : a v <;>
        simp [hsrc,hav,E2.CompilerRealize.sign,neg_mul,hv]
  simp only [controlled,add_mul,sub_mul,one_mul,mul_assoc,hS,Algebra.mul_smul_comm,hj]
  have hh : selector=a ∘ port ↔ ∀ i, a (port i)=selector i := by
    constructor
    · intro h i; exact (congrFun h i).symm
    · intro h; funext i; exact (h i).symm
  by_cases h : selector=a ∘ port
  · simp only [h,↓reduceIte,hh.mp h,sub_self,zero_add]
    rw [ite_eq_left (show ∀ _ : Fin n, True from fun _ => True.intro)]
  · simp [h,← hh,E2.CompilerRealize.sign]

end
end E2.CompilerUpper



