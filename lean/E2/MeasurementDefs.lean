import E2.Clock
import E2.RecordingBounds

namespace E2
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

structure Measurement (d : ℕ) where
  outcomes : ℕ
  arity : outcomes = 2 ∨ outcomes = 3
  projection : Fin outcomes → Mat d
  selfadjoint : ∀ a, (projection a).conjTranspose = projection a
  idempotent : ∀ a, projection a * projection a = projection a
  orthogonal : ∀ a b, a ≠ b → projection a * projection b = 0
  complete : ∑ a, projection a = 1

def Measurement.index {d : ℕ} (p : Measurement d) (k : ℕ) : Fin p.outcomes :=
  ⟨k % p.outcomes, Nat.mod_lt _ (by rcases p.arity with h | h <;> omega)⟩

def Measurement.swap {d : ℕ} (p : Measurement d) : Equiv.Perm (Fin p.outcomes) :=
  Equiv.swap (p.index (if p.outcomes = 2 then 0 else 1))
    (p.index (if p.outcomes = 2 then 1 else 2))

def Measurement.active {d : ℕ} (p : Measurement d) : Mat d :=
  if p.outcomes = 3 then 1 - p.projection (p.index 0) else 1

def TriangularRelations {d m : ℕ} (s : State d) (η : ℝ)
    (p : Fin m → Measurement d) (u : Fin m → Mat d) : Prop :=
  (∀ i, Domain.unitary.Holds (u i)) ∧
  (∀ i a, hs (comm ((p i).projection a) s.xi) ≤ η) ∧
  (∀ i j, i ≠ j → ∀ a b, weighted s (comm ((p i).projection a) ((p j).projection b)) ≤ η) ∧
  (∀ i, hs (comm (u i) s.xi) ≤ η) ∧
  (∀ i a, weighted s (u i * (p i).projection a - (p i).projection ((p i).swap a) * u i) ≤ η) ∧
  (∀ i j, i < j → ∀ a, weighted s (comm (u i) ((p j).projection a)) ≤ η)

def binaryCount {d m : ℕ} (p : Fin m → Measurement d) : ℕ :=
  (Finset.univ.filter (fun i => (p i).outcomes = 2)).card
def activeSum {d m : ℕ} (s : State d) (p : Fin m → Measurement d) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => (p i).outcomes = 3), expectation s (p i).active
def binaryEntropy (x : ℝ) := Real.binEntropy x / Real.log 2

abbrev RecordType {d m : ℕ} (p : Fin m → Measurement d) := ∀ i, Fin (p i).outcomes
def recordingWord {d m : ℕ} (p : Fin m → Measurement d) (a : RecordType p) : Mat d :=
  ((List.finRange m).map (fun i => (p i).projection (a i))).reverse.prod
def stackColumn {d c : ℕ} (D : Fin c → Mat d) :
    Matrix (Fin c × Fin d) (Fin d) ℂ := fun ci j => D ci.1 ci.2 j

/-- Equation (8.2): all branches are bounded together, without division by
branch probabilities. Only state commutators of the recording PVMs are used. -/
theorem all_branch_estimate {d m c : ℕ} (s : State d) (η α L : ℝ)
    (p : Fin m → Measurement d) (D : Fin c → Mat d)
    (hη : 0 ≤ η) (hα : 0 ≤ α) (hL : 0 ≤ L)
    (hstate : ∀ i a, hs (comm ((p i).projection a) s.xi) ≤ η)
    (hcolumn : ‖stackColumn D‖ ≤ L)
    (herror : Real.sqrt (∑ k, hs (D k*s.xi)^2) ≤ α) :
    Real.sqrt (∑ a : RecordType p, ∑ k, hs (D k*recordingWord p a*s.xi)^2) ≤
      α+L*m*Real.sqrt 3*η := by
  let P : ∀ i : Fin m, Fin (p i).outcomes → Mat d := fun i => (p i).projection
  have hP (i : Fin m) : (∑ a, (P i a).conjTranspose*P i a)=1 := by
    simpa only [P,(p i).selfadjoint,(p i).idempotent] using (p i).complete
  have hPc (i : Fin m) : (∑ a, P i a*(P i a).conjTranspose)=1 := by
    simpa only [P,(p i).selfadjoint,(p i).idempotent] using (p i).complete
  have ho (i : Fin m) : (p i).outcomes≤3 := by
    rcases (p i).arity with h | h <;> omega
  have hword (a : RecordType p) : Recording.word P a=recordingWord p a := by
    simp only [Recording.word,List.ofFn_eq_map,recordingWord,P]
  have hbase : hs (Recording.stack D*s.xi)≤α := by
    change hs (Recording.stack (fun k => D k*s.xi))≤α
    rw [Recording.hs_stack_eq_sqrt]
    exact herror
  have h := Recording.recorded_column_bound P hP hPc ho s.xi (Recording.stack D) η α L hη hL
    hstate hcolumn hbase
  simp_rw [hword] at h
  have he : Recording.familyNorm (fun a : RecordType p => Recording.stack D*recordingWord p a*s.xi)=
      Real.sqrt (∑ a : RecordType p, ∑ k, hs (D k*recordingWord p a*s.xi)^2) := by
    change Recording.familyNorm (fun a : RecordType p =>
      Recording.stack (fun k => D k*recordingWord p a*s.xi))=_
    exact Recording.familyNorm_stack_eq_sqrt _
  rw [he] at h
  exact h

end
end E2
