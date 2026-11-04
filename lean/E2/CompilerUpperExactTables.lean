import E2.CompilerUpperContextAssembly

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks
variable {V : Type*} [Fintype V] {d : ℕ}

/-- An outcome is a simultaneous eigenprojection for its own Boolean label. -/
theorem TableMeasurement.eigen {t : Table V} (A : TableMeasurement t d)
    (x : V → Mat d) (hm : ∀ v ∈ t.scope, A.marginal v=decodeProjection (x v))
    (i : Fin A.outcomes) (v : V) (hv : v ∈ t.scope) :
    x v*A.value i=(E2.CompilerRealize.sign (A.label i v):ℂ) • A.value i := by
  classical
  have h : A.marginal v*A.value i=if A.label i v then A.value i else 0 := by
    simp only [TableMeasurement.marginal,Finset.sum_mul,ite_mul,Matrix.zero_mul,A.multiply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [hm v hv] at h
  calc
    _ = (2:ℂ) • (decodeProjection (x v)*A.value i)-A.value i := by
      simp only [decodeProjection,Algebra.smul_mul_assoc,add_mul,one_mul]
      module
    _ = (2:ℂ) • (if A.label i v then A.value i else 0)-A.value i := by rw [h]
    _ = _ := by cases A.label i v <;> simp [E2.CompilerRealize.sign] <;> module

/-- Zero illegal outcomes may be labeled by the table's witness without changing marginals. -/
theorem legalize_measurement (t : Table V) (A : TableMeasurement (free t.scope) d)
    (hz : ∀ i, ¬ t.accepts (A.label i) → A.value i=0) :
    ∃ B : TableMeasurement t d, ∀ v, B.marginal v=A.marginal v := by
  classical
  obtain ⟨a,ha⟩ := t.witness
  let B : TableMeasurement t d := {
    outcomes := A.outcomes
    value := A.value
    label := fun i => if t.accepts (A.label i) then A.label i else a
    domains := A.domains
    multiply := A.multiply
    complete := A.complete
    legal := by intro i; split_ifs with h; exact h; exact ha }
  refine ⟨B,fun v => Finset.sum_congr rfl (fun i _ => ?_)⟩
  change (if (if t.accepts (A.label i) then A.label i else a) v then A.value i else 0)=_
  by_cases h : t.accepts (A.label i)
  · simp [h]
  · simp [h,hz i h]

/-- A commuting exact truth-table representation yields legal original-label PVMs. -/
theorem exact_table_measurement (t : Table V) (x : V → Mat d)
    (hx : ∀ v ∈ t.scope, Domain.reflection.Holds (x v))
    (hc : ∀ v ∈ t.scope, ∀ w ∈ t.scope, Commute (x v) (x w))
    (hz : ∀ (a : V → Bool) (J : Mat d),
      (∀ v ∈ t.scope, x v*J=(E2.CompilerRealize.sign (a v):ℂ) • J) →
      ¬ t.accepts a → J=0) :
    ∃ A : TableMeasurement t d, ∀ v ∈ t.scope, A.marginal v=decodeProjection (x v) := by
  obtain ⟨A,hA⟩ := free_measurement t.scope x hx hc
  obtain ⟨B,hB⟩ := legalize_measurement t A (fun i => hz (A.label i) (A.value i)
    (A.eigen x hA i))
  exact ⟨B,fun v hv => (hB v).trans (hA v hv)⟩

/-- Any parity triple, including repeated symbolic ports, has exact local marginals. -/
theorem parity_measurement (a b c : V) (x : V → Mat d)
    (ha : Domain.reflection.Holds (x a)) (hb : Domain.reflection.Holds (x b))
    (hc : Domain.reflection.Holds (x c)) (ht : ParityTriple (x a) (x b) (x c)) :
    ∃ A : TableMeasurement (parity a b c) d,
      ∀ v ∈ (parity a b c).scope, A.marginal v=decodeProjection (x v) := by
  apply exact_table_measurement
  · intro v hv
    simp only [parity,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · intro v hv w hw
    simp only [parity,Finset.mem_insert,Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact Commute.refl _
    · exact ht.1
    · exact ht.2.1
    · exact (Commute.symm ht.1)
    · exact Commute.refl _
    · exact ht.2.2.1
    · exact (Commute.symm ht.2.1)
    · exact (Commute.symm ht.2.2.1)
    · exact Commute.refl _
  · intro l J he hbad
    have heq : x a=x b*x c := by
      have h := congrArg (fun M => x a*M) ht.2.2.2
      simpa only [← mul_assoc,ha.2,one_mul,mul_one] using h.symm
    have h := he a (by simp [parity])
    rw [heq,mul_assoc,he c (by simp [parity]),Algebra.mul_smul_comm,
      he b (by simp [parity]),smul_smul] at h
    change ¬ E2.CompilerRealize.sign (l a)=E2.CompilerRealize.sign (l b)*E2.CompilerRealize.sign (l c) at hbad
    have hs : (((E2.CompilerRealize.sign (l c):ℂ)*(E2.CompilerRealize.sign (l b):ℂ))-
        (E2.CompilerRealize.sign (l a):ℂ)) • J=0 := by
      rw [sub_smul,h,sub_self]
    apply (smul_eq_zero.mp hs).resolve_left
    intro hh
    apply hbad
    have hr : E2.CompilerRealize.sign (l c)*E2.CompilerRealize.sign (l b)=E2.CompilerRealize.sign (l a) := by
      exact_mod_cast sub_eq_zero.mp hh
    rw [← hr,mul_comm]

end
end E2.CompilerUpper
