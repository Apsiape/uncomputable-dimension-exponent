import E2.BooleanStrategyDilation
import E2.BooleanRealignment
import E2.BooleanGameLoss

namespace E2.BooleanBridgeData
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
open E2.CompilerStrategy E2.BooleanExtraction E2.CompilerDomains

section Transport
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def transport (e : α ≃ β) (M : Matrix α α ℂ) : Matrix β β ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ e M

@[simp] theorem transport_mul (e : α ≃ β) (M N : Matrix α α ℂ) :
    transport e (M*N) = transport e M * transport e N :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul M N

@[simp] theorem transport_add (e : α ≃ β) (M N : Matrix α α ℂ) :
    transport e (M+N) = transport e M + transport e N :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_add M N

@[simp] theorem transport_one (e : α ≃ β) : transport e (1 : Matrix α α ℂ) = 1 :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_one

@[simp] theorem transport_zero (e : α ≃ β) : transport e (0 : Matrix α α ℂ) = 0 :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_zero

@[simp] theorem transport_sum {ι : Type*} (e : α ≃ β) (S : Finset ι) (f : ι → Matrix α α ℂ) :
    transport e (∑ i ∈ S, f i) = ∑ i ∈ S, transport e (f i) :=
  map_sum (Matrix.reindexAlgEquiv ℂ ℂ e) f S

@[simp] theorem transport_star (e : α ≃ β) (M : Matrix α α ℂ) :
    (transport e M).conjTranspose = transport e M.conjTranspose := by
  simp [transport, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]

@[simp] theorem transport_trace (e : α ≃ β) (M : Matrix α α ℂ) :
    Matrix.trace (transport e M) = Matrix.trace M :=
  e.symm.sum_comp (fun i => M i i)

 theorem transport_positive (e : α ≃ β) (M : Matrix α α ℂ) (h : M.PosSemidef) :
    (transport e M).PosSemidef := h.submatrix _
end Transport

variable {G : BCSGame} {d : ℕ}

abbrev adim (G : BCSGame) (d : ℕ) := Fintype.card (BooleanStrategyDilation.AliceSpace G d)
abbrev bdim (d : ℕ) := Fintype.card (BooleanStrategyDilation.BobSpace d)
def ae (G : BCSGame) (d : ℕ) := Fintype.equivFin (BooleanStrategyDilation.AliceSpace G d)
def be (d : ℕ) := Fintype.equivFin (BooleanStrategyDilation.BobSpace d)

def alice (s : Strategy G d) (c : Fin G.contexts) (x : Fin G.numVars → Bool) : Mat (adim G d) :=
  transport (ae G d) (BooleanStrategyDilation.alice s c x)
def bob (s : Strategy G d) (v : Fin G.numVars) (b : Bool) : Mat (bdim d) :=
  transport (be d) (BooleanStrategyDilation.bob s v b)
def rho (s : Strategy G d) : Matrix (Fin (adim G d) × Fin (bdim d))
    (Fin (adim G d) × Fin (bdim d)) ℂ :=
  transport ((ae G d).prodCongr (be d)) (BooleanStrategyDilation.rho s)

theorem rho_positive (s : Strategy G d) : (rho s).PosSemidef :=
  transport_positive _ _ (BooleanStrategyDilation.rho_positive s)
theorem rho_trace (s : Strategy G d) : Matrix.trace (rho s) = 1 := by
  rw [rho,transport_trace,BooleanStrategyDilation.rho_trace]

theorem alice_hermitian (s : Strategy G d) (c x) : (alice s c x).conjTranspose = alice s c x := by
  simp [alice,BooleanStrategyDilation.alice_hermitian]
theorem alice_mul (s : Strategy G d) (c x y) :
    alice s c x * alice s c y = if x=y then alice s c x else 0 := by
  rw [alice,alice,← transport_mul,BooleanStrategyDilation.alice_mul]
  split_ifs <;> simp [alice]
theorem alice_sum (s : Strategy G d) (c) : (∑ x, alice s c x) = 1 := by
  simpa [alice] using congrArg (transport (ae G d)) (BooleanStrategyDilation.alice_sum s c)

theorem bob_projection (s : Strategy G d) (v b) : Domain.projection.Holds (bob s v b) := by
  constructor
  · simp [bob,BooleanStrategyDilation.bob_hermitian]
  · simp only [bob,← transport_mul,BooleanStrategyDilation.bob_mul,ite_true]

theorem bob_sum (s : Strategy G d) (v) : (∑ b, bob s v b) = 1 := by
  simpa [bob] using congrArg (transport (be d)) (BooleanStrategyDilation.bob_sum s v)

theorem correlation (s : Strategy G d) (c x v b) :
    Matrix.trace (rho s * Matrix.kronecker (alice s c x) (bob s v b)) =
    Matrix.trace (s.rho * Matrix.kronecker (s.alice c x) (s.bob v b)) := by
  have hk : Matrix.kronecker (alice s c x) (bob s v b) =
      transport ((ae G d).prodCongr (be d))
        (Matrix.kronecker (BooleanStrategyDilation.alice s c x) (BooleanStrategyDilation.bob s v b)) := by
    rfl
  rw [hk,rho,← transport_mul,transport_trace,BooleanStrategyDilation.correlation]

def legalize (G : BCSGame) (c : Fin G.contexts) (x : Fin G.numVars → Bool) : Fin G.numVars → Bool :=
  if x ∈ G.allowed c then x else (G.valid_nonempty c).choose

theorem legalize_mem (G : BCSGame) (c x) : legalize G c x ∈ G.allowed c := by
  unfold legalize
  split_ifs with h
  · exact h
  · exact (G.valid_nonempty c).choose_spec

def legalPVM (s : Strategy G d) : ContextPVM G (adim G d) :=
  ContextPVM.ofOutcomes (fun _ => Fintype.card (Fin G.numVars → Bool))
    (fun c i => alice s c ((Fintype.equivFin _).symm i))
    (fun c i => legalize G c ((Fintype.equivFin _).symm i))
    (fun c i => ⟨alice_hermitian s c _,by simpa using (alice_mul s c
      ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm i))⟩)
    (by
      intro c i j
      rw [alice_mul]
      simp only [Equiv.apply_eq_iff_eq])
    (by
      intro c
      rw [(Fintype.equivFin (Fin G.numVars → Bool)).symm.sum_comp]
      exact alice_sum s c)
    (fun c i => legalize_mem G c _)

end
end E2.BooleanBridgeData
