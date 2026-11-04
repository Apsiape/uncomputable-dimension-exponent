import E2.JointEffects

namespace E2
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator

def binaryMeasurement {d : ℕ} (P : Mat d) (hP : Domain.projection.Holds P) : Measurement d where
  outcomes := 2
  arity := Or.inl rfl
  projection := fun a => if a.val=0 then P else 1-P
  selfadjoint := by intro a; fin_cases a; exact hP.1; exact (projection_complement hP).1
  idempotent := by intro a; fin_cases a; exact hP.2; exact (projection_complement hP).2
  orthogonal := by
    intro a b hab; fin_cases a <;> fin_cases b
    all_goals first | exact False.elim (hab rfl) |
      (change P*(1-P)=0; rw [Matrix.mul_sub,Matrix.mul_one,hP.2,sub_self]) |
      (change (1-P)*P=0; rw [Matrix.sub_mul,Matrix.one_mul,hP.2,sub_self])
  complete := by simp [Fin.sum_univ_succ]

def slotMeasurement {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) : Bool → Measurement d
  | true => conditionalMeasurement F R hF hR hFR
  | false => binaryMeasurement (1-R) (projection_complement hR)

def slotCode {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) (t : Bool) :
    Fin (slotMeasurement F R hF hR hFR t).outcomes → Fin 3 := by
  cases t
  · exact fun a => ⟨a.val+1,by have := a.isLt; change a.val < 2 at this; omega⟩
  · exact id

theorem slot_effect {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) (t : Bool) (ht : t=false → F=1)
    (a : Fin (slotMeasurement F R hF hR hFR t).outcomes) :
    (slotMeasurement F R hF hR hFR t).projection a=
      ternaryEffect F R (slotCode F R hF hR hFR t a) := by
  cases t
  · have h := ht rfl
    fin_cases a <;> simp [slotMeasurement,binaryMeasurement,slotCode,ternaryEffect,h]
  · fin_cases a <;> rfl

theorem slot_swap_effect {d : ℕ} (F R : Mat d) (hF : Domain.projection.Holds F)
    (hR : Domain.projection.Holds R) (hFR : F*R=R) (t : Bool) (ht : t=false → F=1)
    (a : Fin (slotMeasurement F R hF hR hFR t).outcomes) :
    (slotMeasurement F R hF hR hFR t).projection ((slotMeasurement F R hF hR hFR t).swap a)=
      ternaryEffect F R (ternarySwap (slotCode F R hF hR hFR t a)) := by
  cases t
  · have h := ht rfl
    fin_cases a
    · change 1-(1-R)=R
      abel
    · change 1-R=F-R
      rw [h]
  · fin_cases a <;> rfl

structure RawSlot (d : ℕ) where
  flag : Mat d
  datum : Mat d
  flip : Mat d
  flag_domain : Domain.projection.Holds flag
  data_domain : Domain.projection.Holds datum
  flip_domain : Domain.reflection.Holds flip
  ternary : Bool
  binary_flag : ternary=false → flag=1

def RawSlot.selected {d : ℕ} (x : RawSlot d) (b : Bool) : Mat d := if b then x.datum else x.flag
theorem RawSlot.selected_domain {d : ℕ} (x : RawSlot d) (b : Bool) :
    Domain.projection.Holds (x.selected b) := by cases b; exact x.flag_domain; exact x.data_domain

structure SlotBounds {d n : ℕ} (s : State d) (η : ℝ) (x : Fin n → RawSlot d) : Prop where
  state : ∀ i b, hs (comm ((x i).selected b) s.xi) ≤ η
  flip_state : ∀ i, hs (comm (x i).flip s.xi) ≤ η
  pair : ∀ i j, i ≠ j → ∀ b c, weighted s (comm ((x i).selected b) ((x j).selected c)) ≤ η
  own : ∀ i b, weighted s ((x i).flip*(x i).selected b*(x i).flip-
    (if b then (x i).flag-(x i).datum else (x i).flag)) ≤ η
  later : ∀ i j, i < j → ∀ b, weighted s (comm (x i).flip ((x j).selected b)) ≤ η
  inclusion : ∀ i, weighted s ((1-(x i).flag)*(x i).datum) ≤ η

structure ExactSlot (d : ℕ) extends RawSlot d where
  included : flag*datum=datum

def ExactSlot.measurement {d : ℕ} (x : ExactSlot d) : Measurement d :=
  slotMeasurement x.flag x.datum x.flag_domain x.data_domain x.included x.ternary

/-- Exact PVM conversion, preserving the raw activation flag and the ordered flip. -/
theorem exact_slots_triangular {d n : ℕ} (s : State d) (η : ℝ) (hη : 0 ≤ η)
    (x : Fin n → ExactSlot d) (h : SlotBounds s η (fun i => (x i).toRawSlot)) :
    TriangularRelations s (4*η) (fun i => (x i).measurement) (fun i => (x i).flip) := by
  let hc (i : Fin n) (a : Fin (x i).measurement.outcomes) : Fin 3 :=
    slotCode (x i).flag (x i).datum (x i).flag_domain (x i).data_domain
      (x i).included (x i).ternary a
  have he (i : Fin n) (a : Fin (x i).measurement.outcomes) :
      (x i).measurement.projection a=ternaryEffect (x i).flag (x i).datum (hc i a) :=
    slot_effect _ _ _ _ _ _ (x i).binary_flag a
  have hswap (i : Fin n) (a : Fin (x i).measurement.outcomes) :
      (x i).measurement.projection ((x i).measurement.swap a)=
        ternaryEffect (x i).flag (x i).datum (ternarySwap (hc i a)) :=
    slot_swap_effect _ _ _ _ _ _ (x i).binary_flag a
  refine ⟨fun i => reflection_unitary _ (x i).flip_domain,?_,?_,?_,?_,?_⟩
  · intro i a
    change hs (comm ((x i).measurement.projection a) s.xi) ≤ _
    rw [he i a]
    exact (effect_state s _ _ η hη (h.state i false) (h.state i true) (hc i a)).trans (by linarith)
  · intro i j hij a b
    change weighted s (comm ((x i).measurement.projection a)
      ((x j).measurement.projection b)) ≤ _
    rw [he i a,he j b]
    exact effect_comm_pair s _ _ _ _ η hη (h.pair i j hij false false)
      (h.pair i j hij false true) (h.pair i j hij true false) (h.pair i j hij true true) _ _
  · intro i; exact (h.flip_state i).trans (by linarith)
  · intro i a
    change weighted s ((x i).flip*((x i).measurement.projection a)-
      ((x i).measurement.projection ((x i).measurement.swap a))*(x i).flip) ≤ _
    rw [he i a,hswap i a]
    exact effect_own_intertwining s _ _ _ (x i).flag_domain (x i).data_domain
      (x i).included (x i).flip_domain η hη (h.flip_state i) (h.own i false) (h.own i true) _
  · intro i j hij a
    change weighted s (comm (x i).flip ((x j).measurement.projection a)) ≤ _
    rw [he j a]
    exact (effect_comm_right s _ _ _ η hη (h.later i j hij false) (h.later i j hij true) _).trans (by linarith)

/-- The complete repair step is independent at each slot. Binary data stay exact. -/
theorem repair_slots {d n : ℕ} (s : State d) (η : ℝ) (hη : 0 ≤ η)
    (x : Fin n → RawSlot d) (h : SlotBounds s η x) :
    ∃ y : Fin n → ExactSlot d,
      (∀ i, (y i).flag=(x i).flag ∧ (y i).flip=(x i).flip ∧ (y i).ternary=(x i).ternary) ∧
      (∀ i, (x i).ternary=false → (y i).datum=(x i).datum) ∧
      (∀ i, weighted s ((y i).datum-(x i).datum) ≤ 6*η) ∧
      SlotBounds s (53*η) (fun i => (y i).toRawSlot) := by
  classical
  have hex (i : Fin n) : ∃ R : Mat d, Domain.projection.Holds R ∧ (x i).flag*R=R ∧
      weighted s (R-(x i).datum) ≤ 6*η ∧ hs (comm R s.xi) ≤ 13*η ∧
      ((x i).ternary=false → R=(x i).datum) := by
    by_cases ht : (x i).ternary=true
    · obtain ⟨R,hR,hFR,hc,hs⟩ := projection_inclusion_repair_state s (state_dimension_pos s)
        (x i).flag (x i).datum (x i).flag_domain (x i).data_domain η hη
        (h.inclusion i) (h.state i false) (h.state i true)
      exact ⟨R,hR,hFR,hc,hs,by simp [ht]⟩
    · have hf : (x i).ternary=false := by cases hb : (x i).ternary <;> simp_all
      refine ⟨(x i).datum,(x i).data_domain,?_,?_,?_,fun _ => rfl⟩
      · rw [(x i).binary_flag hf,Matrix.one_mul]
      · rw [sub_self,weighted_zero_eq]; positivity
      · exact (h.state i true).trans (by linarith)
  choose R hR hFR hclose hstate hbinary using hex
  let y : Fin n → ExactSlot d := fun i =>
    { flag := (x i).flag, datum := R i, flip := (x i).flip, flag_domain := (x i).flag_domain,
      data_domain := hR i, flip_domain := (x i).flip_domain, ternary := (x i).ternary,
      binary_flag := (x i).binary_flag, included := hFR i }
  have hnD (i : Fin n) (b : Bool) : ‖(y i).selected b-(x i).selected b‖ ≤ 2 := by
    have h1 := projection_norm_le ((y i).selected_domain b)
    have h2 := projection_norm_le ((x i).selected_domain b)
    exact (norm_sub_le _ _).trans (by linarith)
  have hcD (i : Fin n) (b : Bool) : weighted s ((y i).selected b-(x i).selected b) ≤ 6*η := by
    cases b
    · change weighted s ((x i).flag-(x i).flag) ≤ _
      rw [sub_self,weighted_zero_eq]; positivity
    · exact hclose i
  have hσ (i : Fin n) (b : Bool) : hs (comm ((y i).selected b) s.xi) ≤ 13*η := by
    cases b
    · exact (h.state i false).trans (by linarith)
    · exact hstate i
  refine ⟨y,fun _ => ⟨rfl,rfl,rfl⟩,hbinary,hclose,?_⟩
  refine ⟨fun i b => (hσ i b).trans (by linarith),?_,?_,?_,?_,?_⟩
  · intro i; exact (h.flip_state i).trans (by linarith)
  · intro i j hij b c
    exact joint_commutator_replacements s η _ _ _ _
      (projection_norm_le ((x i).selected_domain b)) (projection_norm_le ((y j).selected_domain c))
      (hnD i b) (hnD j c) (hcD i b) (hcD j c) (h.state i b) (hσ j c) (h.pair i j hij b c)
  · intro i b; cases b
    · exact (h.own i false).trans (by linarith)
    · have hr := joint_own_replacement s η (x i).flip (x i).flag (x i).datum (R i)
        (unitary_norm (state_dimension_pos s) (reflection_unitary _ (x i).flip_domain)).le
        (hnD i true) (hclose i) (h.flip_state i) (h.own i true)
      exact hr.trans (by linarith)
  · intro i j hij b
    have hr := joint_later_replacement s η (x i).flip ((x j).selected b) ((y j).selected b)
      (unitary_norm (state_dimension_pos s) (reflection_unitary _ (x i).flip_domain)).le
      (hnD j b) (hcD j b) (h.flip_state i) (h.later i j hij b)
    exact hr.trans (by linarith)
  · intro i
    have he : (1-(y i).flag)*(y i).datum=0 := by
      rw [Matrix.sub_mul,Matrix.one_mul,(y i).included,sub_self]
    rw [he,weighted_zero_eq]; positivity

end
end E2
