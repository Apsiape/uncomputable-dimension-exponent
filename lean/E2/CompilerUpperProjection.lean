import E2.CompilerPauliExtension
import E2.CompilerMultiSelector

namespace E2.CompilerUpper
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open E2.CompilerBoolean E2.CompilerMultiSelector E2.CompilerDomains E2.CompilerBlocks
variable {d n : ℕ}

theorem projection_mul (P Q : Mat d) (hP : Domain.projection.Holds P)
    (hQ : Domain.projection.Holds Q) (hc : Commute P Q) : Domain.projection.Holds (P*Q) := by
  constructor
  · simpa only [Matrix.conjTranspose_mul,hP.1,hQ.1] using hc.eq.symm
  · calc
      _ = P*(Q*P)*Q := by simp only [mul_assoc]
      _ = P*(P*Q)*Q := by rw [hc.eq]
      _ = P*Q := by rw [← mul_assoc P P Q,hP.2,mul_assoc,hQ.2]

theorem atom_domain (X : Mat d) (hX : Domain.reflection.Holds X) (b : Bool) :
    Domain.projection.Holds (E2.CompilerBoolean.atom X b) := by
  cases b
  · have hN : Domain.reflection.Holds (-X) := by
      constructor
      · simp [hX.1]
      · simpa using hX.2
    simpa only [E2.CompilerBoolean.atom,Bool.false_eq_true,↓reduceIte,decodeProjection,sub_eq_add_neg] using decode_projection (-X) hN
  · exact decode_projection X hX

theorem atom_commutes (X Y : Mat d) (hc : Commute X Y) (a b : Bool) :
    Commute (E2.CompilerBoolean.atom X a) (E2.CompilerBoolean.atom Y b) := by
  cases a <;> cases b <;> dsimp only [E2.CompilerBoolean.atom] <;>
    apply Commute.smul_left <;> apply Commute.smul_right
  · exact (Commute.one_right _).sub_right ((Commute.one_left Y).sub_left hc)
  · exact (Commute.one_right _).add_right ((Commute.one_left Y).sub_left hc)
  · exact (Commute.one_right _).sub_right ((Commute.one_left Y).add_left hc)
  · exact (Commute.one_right _).add_right ((Commute.one_left Y).add_left hc)

theorem joint_domain (x : Fin n → Mat d) (hx : ∀ i, Domain.reflection.Holds (x i))
    (hc : ∀ i j, Commute (x i) (x j)) (a : Fin n → Bool) :
    Domain.projection.Holds (E2.CompilerBoolean.joint x a) := by
  induction n with
  | zero => simp [E2.CompilerBoolean.joint,Domain.Holds]
  | succ n ih =>
    unfold E2.CompilerBoolean.joint
    rw [E2.CompilerBoolean.ordered_succ]
    apply projection_mul
    · exact atom_domain (x 0) (hx 0) (a 0)
    · exact ih (fun i => x i.succ) (fun i => hx i.succ) (fun i j => hc i.succ j.succ) _
    · apply commute_ordered
      intro i
      exact atom_commutes _ _ (hc 0 i.succ) _ _

theorem commute_atom (M X : Mat d) (hc : Commute M X) (b : Bool) :
    Commute M (E2.CompilerBoolean.atom X b) := by
  cases b
  · exact ((Commute.one_right M).sub_right hc).smul_right _
  · exact ((Commute.one_right M).add_right hc).smul_right _

theorem commute_joint (M : Mat d) (x : Fin n → Mat d) (hc : ∀ i, Commute M (x i)) (a : Fin n → Bool) :
    Commute M (E2.CompilerBoolean.joint x a) := by
  apply commute_ordered
  intro i
  exact commute_atom _ _ (hc i) _

/-- Canonical successive conjugation keeps every variable an exact reflection. -/
def conjugateList (L : List (Mat d)) (R : Mat d) : Mat d :=
  L.foldl (fun M A => A*M*A) R

theorem conjugateList_domain (L : List (Mat d)) (hL : ∀ A ∈ L, Domain.reflection.Holds A)
    (R : Mat d) (hR : Domain.reflection.Holds R) : Domain.reflection.Holds (conjugateList L R) := by
  induction L generalizing R with
  | nil => exact hR
  | cons A L ih =>
    apply ih (fun B hB => hL B (by simp [hB]))
    exact reflection_conjugate (hL A (by simp)) hR

@[simp] theorem conjugateList_append (L M : List (Mat d)) (R : Mat d) :
    conjugateList (L++M) R=conjugateList M (conjugateList L R) := List.foldl_append ..

end
end E2.CompilerUpper
