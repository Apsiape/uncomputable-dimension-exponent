import E2.CompilerUpperRepair
import E2.CompilerStrategy

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks E2.FiniteConstruction Companion.Analytic
variable {V : Type*} [Fintype V] {d : ℕ}

/-- Finite legal local PVM data with labels in the original total-assignment type. -/
structure TableMeasurement (t : Table V) (d : ℕ) where
  outcomes : ℕ
  value : Fin outcomes → Mat d
  label : Fin outcomes → (V → Bool)
  domains : ∀ i, Domain.projection.Holds (value i)
  multiply : ∀ i j, value i*value j=if i=j then value i else 0
  complete : ∑ i, value i=1
  legal : ∀ i, t.accepts (label i)

def TableMeasurement.marginal {t : Table V} (A : TableMeasurement t d) (v : V) : Mat d :=
  ∑ i, if A.label i v then A.value i else 0

/-- Original total assignment labels for the three legal orthogonality outcomes. -/
theorem orthogonal_measurement (e f : V) (hef : e≠f) (E R : Mat d)
    (hE : Domain.projection.Holds E) (hR : Domain.projection.Holds R)
    (hER : E*R=0) (hRE : R*E=0) :
    ∃ A : TableMeasurement (orthogonal e f) d, A.outcomes=3 ∧
      A.marginal e=E ∧ A.marginal f=R := by
  classical
  obtain ⟨hrest,hsum,hEt,hRt,htE,htR⟩ :=
    E2.CompilerOrthogonality.orthogonality_pvm E R hE hR hER hRE
  let M : Fin 3 → Mat d := ![E,R,1-E-R]
  let L : Fin 3 → (V → Bool) := ![fun v => decide (v=e),fun v => decide (v=f),fun _ => false]
  have hdom (i) : Domain.projection.Holds (M i) := by
    fin_cases i
    · exact hE
    · exact hR
    · exact hrest
  have hmul (i j) : M i*M j=if i=j then M i else 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [M,hE.2,hR.2,hER,hRE,hEt,hRt,htE,htR,hrest.2]
  have hlegal (i) : (orthogonal e f).accepts (L i) := by
    fin_cases i <;> simp [orthogonal,L,hef,Ne.symm hef]
  let A : TableMeasurement (orthogonal e f) d := {
    outcomes := 3
    value := M
    label := L
    domains := hdom
    multiply := hmul
    complete := by simpa [M,Fin.sum_univ_succ,add_assoc] using hsum
    legal := hlegal }
  refine ⟨A,rfl,?_,?_⟩ <;>
    simp [A,TableMeasurement.marginal,M,L,Fin.sum_univ_succ,hef,Ne.symm hef]


/-- Marginals of the full joint PVM are the original decoded reflections. -/
theorem joint_marginal {n : ℕ} (x : Fin n → Mat d)
    (hx : ∀ i, Domain.reflection.Holds (x i)) (hc : ∀ i j, Commute (x i) (x j)) (i : Fin n) :
    (∑ a : Fin n → Bool, if a i then E2.CompilerBoolean.joint x a else 0)=decodeProjection (x i) := by
  have he (a : Fin n → Bool) : decodeProjection (x i)*E2.CompilerBoolean.joint x a =
      if a i then E2.CompilerBoolean.joint x a else 0 := by
    have hh : x i*E2.CompilerBoolean.joint x a=
        (E2.CompilerRealize.sign (a i):ℂ) • E2.CompilerBoolean.joint x a := by
      simpa only [E2.CompilerRealize.joint,rational_atom,E2.CompilerBoolean.joint,rational_smul] using
        E2.CompilerRealize.eigen_joint x (fun i => (hx i).2) hc a i
    simp only [decodeProjection,Algebra.smul_mul_assoc,add_mul,one_mul,hh]
    cases ha : a i <;> simp [ha,E2.CompilerRealize.sign] <;> module
  simp_rw [← he]
  rw [← Finset.mul_sum,E2.CompilerBoolean.joint_partition,mul_one]

/-- Every free table has a legal PVM in the original total symbolic labels. -/
theorem free_measurement (S : Finset V) (x : V → Mat d)
    (hx : ∀ v ∈ S, Domain.reflection.Holds (x v))
    (hc : ∀ v ∈ S, ∀ w ∈ S, Commute (x v) (x w)) :
    ∃ A : TableMeasurement (free S) d, ∀ v ∈ S, A.marginal v=decodeProjection (x v) := by
  classical
  let n := S.toList.length
  let port : Fin n → V := S.toList.get
  have hinj : Function.Injective port := (Finset.nodup_toList S).injective_get
  have hmem (i : Fin n) : port i ∈ S := Finset.mem_toList.mp (List.get_mem _ _)
  let z : Fin n → Mat d := fun i => x (port i)
  have hz (i) := hx (port i) (hmem i)
  have hzz (i j) := hc (port i) (hmem i) (port j) (hmem j)
  let e := Fintype.equivFin (Fin n → Bool)
  let M : Fin (Fintype.card (Fin n → Bool)) → Mat d :=
    fun i => E2.CompilerBoolean.joint z (e.symm i)
  let L : Fin (Fintype.card (Fin n → Bool)) → (V → Bool) :=
    fun i => Function.extend port (e.symm i) (fun _ => true)
  have hm (i j) : M i*M j=if i=j then M i else 0 := by
    simp only [M,joint_mul z hz hzz,e.symm.injective.eq_iff]
  have hs : ∑ i, M i=1 := by
    rw [show (∑ i, M i) = ∑ a : Fin n → Bool, E2.CompilerBoolean.joint z a from
      (e.sum_comp (fun i => M i)).symm.trans (by simp only [M,Equiv.symm_apply_apply])]
    exact E2.CompilerBoolean.joint_partition z
  let A : TableMeasurement (free S) d := {
    outcomes := Fintype.card (Fin n → Bool)
    value := M
    label := L
    domains := fun i => joint_domain z hz hzz _
    multiply := hm
    complete := hs
    legal := by simp [free] }
  refine ⟨A,?_⟩
  intro v hv
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hv)
  change port i=v at hi
  subst v
  change (∑ j, if L j (port i) then M j else 0)=_
  simp only [L,hinj.extend_apply]
  rw [show (∑ j, if (e.symm j) i then M j else 0)=
      ∑ a : Fin n → Bool, if a i then E2.CompilerBoolean.joint z a else 0 from
    (e.sum_comp (fun j => if (e.symm j) i then M j else 0)).symm.trans
      (by simp only [M,Equiv.symm_apply_apply])]
  exact joint_marginal z hz hzz i

/-- Relabel local measurement outcomes along the actual game's equivalence. -/
def TableMeasurement.relabel {t : Table V} (A : TableMeasurement t d) :
    TableMeasurement t.relabel d where
  outcomes := A.outcomes
  value := A.value
  label i v := A.label i ((Fintype.equivFin V).symm v)
  domains := A.domains
  multiply := A.multiply
  complete := A.complete
  legal i := by
    change t.accepts (fun v => A.label i ((Fintype.equivFin V).symm (Fintype.equivFin V v)))
    simpa only [Equiv.symm_apply_apply] using A.legal i

@[simp] theorem TableMeasurement.relabel_marginal {t : Table V}
    (A : TableMeasurement t d) (v : V) :
    A.relabel.marginal (Fintype.equivFin V v)=A.marginal v := by
  simp only [TableMeasurement.marginal,TableMeasurement.relabel,Equiv.symm_apply_apply]

/-- The signed constant letter makes every relation's control chain nonempty. -/
theorem steps_pos {ι : Type*} [Fintype ι] (P : Presentation ι) (r : Fin P.relations.length) :
    0<steps P r := by
  classical
  let a : Fin (q P r) → Bool := fun _ => true
  let t := (packedWords (relationWords P r)).getD (Fintype.equivFin _ a).val (true,[])
  have hm : (⟨a,none,t.1⟩ : Letter (ι × Fin 2) (q P r)) ∈ letters (relationWords P r) := by
    unfold letters
    exact List.mem_flatMap.mpr ⟨a,by simp,List.mem_cons_self⟩
  exact List.length_pos_of_mem hm

theorem E_ne_F {ι : Type*} [Fintype ι] (P : Presentation ι) (r : Fin P.relations.length) :
    E P r≠F P r := by
  have h := steps_pos P r
  simp [F,show steps P r≠0 by omega,E,E2.CompilerNetwork.conjugate,localWire]

/-- Step 4 for the actual repaired orthogonality tables. -/
theorem actual_orthogonal_measurement {ι : Type*} [Fintype ι]
    (P : Presentation ι) (s : ι × Fin 2 → Mat d)
    (aux : GadgetKey P → GadgetWire → Mat (2*(2*(CompilerUpper.registerSize P*d))))
    (r : Fin P.relations.length) (R : Mat (2*(2*(CompilerUpper.registerSize P*d))))
    (hE : Domain.projection.Holds (decodeProjection (wireValue P s aux (E P r))))
    (hR : Domain.projection.Holds R)
    (hER : decodeProjection (wireValue P s aux (E P r))*R=0)
    (hRE : R*decodeProjection (wireValue P s aux (E P r))=0) :
    ∃ A : TableMeasurement (orthogonal (E P r) (F P r)) (2*(2*(registerSize P*d))),
      A.outcomes=3 ∧ A.marginal (E P r)=decodeProjection (wireValue P s aux (E P r)) ∧
      A.marginal (F P r)=R :=
  orthogonal_measurement _ _ (E_ne_F P r) _ _ hE hR hER hRE

end
end E2.CompilerUpper
