import E2.FiniteGuardedIncrement
import E2.FiniteDressedShift
import Mathlib.Data.Vector.Basic

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

abbrev BinaryWord (N : ℕ) := List.Vector Bool N

instance binaryWordFintype (N : ℕ) : Fintype (BinaryWord N) :=
  Fintype.ofEquiv (Fin N → Bool) (Equiv.vectorEquivFin Bool N).symm

def listDecrement : List Bool → List Bool
  | [] => []
  | true::bs => false::bs
  | false::bs => true::listDecrement bs

theorem listDecrement_length (bs : List Bool) : (listDecrement bs).length=bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [listDecrement,ih]

theorem listDecrement_increment (bs : List Bool) : listDecrement (listIncrement bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [listDecrement,listIncrement,ih]

theorem listIncrement_decrement (bs : List Bool) : listIncrement (listDecrement bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [listDecrement,listIncrement,ih]

def incrementWord (N : ℕ) : Equiv.Perm (BinaryWord N) where
  toFun b := ⟨listIncrement b.val,(listIncrement_length b.val).trans b.property⟩
  invFun b := ⟨listDecrement b.val,(listDecrement_length b.val).trans b.property⟩
  left_inv b := Subtype.ext (listDecrement_increment b.val)
  right_inv b := Subtype.ext (listIncrement_decrement b.val)

theorem listFlipFirst_length (bs : List Bool) : (listFlipFirst bs).length=bs.length := by
  cases bs <;> rfl

def flipFirstWord (N : ℕ) : Equiv.Perm (BinaryWord N) where
  toFun b := ⟨listFlipFirst b.val,(listFlipFirst_length b.val).trans b.property⟩
  invFun b := ⟨listFlipFirst b.val,(listFlipFirst_length b.val).trans b.property⟩
  left_inv b := by apply Subtype.ext; change listFlipFirst (listFlipFirst b.val)=b.val; cases b.val with | nil => rfl | cons a as => cases a <;> rfl
  right_inv b := by apply Subtype.ext; change listFlipFirst (listFlipFirst b.val)=b.val; cases b.val with | nil => rfl | cons a as => cases a <;> rfl

def recursiveWord (N : ℕ) (b : BinaryWord N) : BinaryWord N :=
  ⟨recursiveIncrement b.val,(recursiveIncrement_length b.val).trans b.property⟩

def twistedIncrement {β : Type*} (N : ℕ) (r : Equiv.Perm β) : Equiv.Perm (BinaryWord N × β) :=
  skewShift (incrementWord N) r (fun z => if z.val.all id then 1 else 0)

def twistedRecursive {β : Type*} (N : ℕ) (r : Equiv.Perm β) (z : BinaryWord N × β) : BinaryWord N × β :=
  (recursiveWord N z.1, if z.1.val.all id then r z.2 else z.2)

def boundaryAlternative {β : Type*} (N : ℕ) (r : Equiv.Perm β) : Equiv.Perm (BinaryWord N × β) :=
  (twistedIncrement N r).trans ((flipFirstWord N).prodCongr (Equiv.refl β))

def graphMatrix {α : Type*} [DecidableEq α] (f : α → α) : Matrix α α ℂ :=
  fun i j => if f i=j then 1 else 0

theorem graphMatrix_perm {α : Type*} [DecidableEq α] (s : Equiv.Perm α) :
    graphMatrix s=s.permMatrix ℂ := by
  ext i j
  simp [graphMatrix,Equiv.Perm.permMatrix,PEquiv.toMatrix,Equiv.toPEquiv_apply]

def onesBoundary {β : Type*} [DecidableEq β] (N : ℕ) : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ :=
  Matrix.diagonal (fun z => if z.1.val.all id then 1 else 0)

def coordinateGuard {β : Type*} [DecidableEq β] (N : ℕ) : Matrix (BinaryWord N × β) (BinaryWord N × β) ℂ :=
  Matrix.diagonal (fun z => ((1-listCoordinate z.1.val:ℝ):ℂ))

/-- Exact residual factorization with an arbitrary optional-register boundary
permutation. The same permutation occurs in both boundary output terms. -/
theorem twisted_guard_boundary {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (r : Equiv.Perm β) :
    coordinateGuard N*((twistedIncrement N r).permMatrix ℂ-graphMatrix (twistedRecursive N r)) =
      (((1/4:ℝ)^N:ℝ):ℂ) •
        (onesBoundary N*((twistedIncrement N r).permMatrix ℂ-(boundaryAlternative N r).permMatrix ℂ)) := by
  rw [←graphMatrix_perm,←graphMatrix_perm]
  ext i j
  simp only [coordinateGuard,onesBoundary,Matrix.diagonal_mul,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases hall : i.1.val.all id = true
  · have hw : recursiveWord N i.1 = flipFirstWord N (incrementWord N i.1) := by
      apply Subtype.ext
      exact (recursiveIncrement_boundary i.1.val).trans (if_pos hall)
    have hr : twistedRecursive N r i = boundaryAlternative N r i := by
      rcases i with ⟨a,b⟩
      simp only [twistedRecursive,boundaryAlternative,Equiv.trans_apply,Equiv.prodCongr_apply,
        Equiv.refl_apply,Prod.map_apply,twistedIncrement,skewShift,Equiv.coe_fn_mk,hall,↓reduceIte,zpow_one,hw]
    have hweight : 1-listCoordinate i.1.val=(1/4:ℝ)^N := by
      rw [listCoordinate_all_ones i.1.val hall,i.1.property]
      ring
    simp [hall,graphMatrix,hr,hweight]
  · have hfalse : i.1.val.all id = false := Bool.eq_false_iff.mpr hall
    have hw : recursiveWord N i.1=incrementWord N i.1 := by
      apply Subtype.ext
      exact recursiveIncrement_interior i.1.val hfalse
    have hr : twistedRecursive N r i = twistedIncrement N r i := by
      rcases i with ⟨a,b⟩
      simp only [twistedRecursive,twistedIncrement,skewShift,Equiv.coe_fn_mk,hfalse,Bool.false_eq_true,↓reduceIte,
        zpow_zero,Equiv.Perm.one_apply,hw]
    simp [hall,graphMatrix,hr]

theorem onesBoundary_norm {β : Type*} [Fintype β] [DecidableEq β] (N : ℕ) :
    ‖onesBoundary (β := β) N‖ ≤ 1 := by
  rw [onesBoundary,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro z
  cases h : z.1.val.all id <;> simp [h]

/-- Operator norm, rather than a maximum column norm. The factor two fits
inside the original source theorem's common constant three. -/
theorem twisted_guard_norm {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (r : Equiv.Perm β) :
    ‖coordinateGuard N*((twistedIncrement N r).permMatrix ℂ-graphMatrix (twistedRecursive N r))‖ ≤
      2*(1/4:ℝ)^N := by
  rw [twisted_guard_boundary,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤(1/4:ℝ)^N)]
  have hu : ‖(twistedIncrement N r).permMatrix ℂ‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le _
  have hv : ‖(boundaryAlternative N r).permMatrix ℂ‖ ≤ 1 := Matrix.permMatrix_l2_opNorm_le _
  have hd : ‖(twistedIncrement N r).permMatrix ℂ-(boundaryAlternative N r).permMatrix ℂ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith)
  have hp : ‖onesBoundary (β := β) N*
      ((twistedIncrement N r).permMatrix ℂ-(boundaryAlternative N r).permMatrix ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖onesBoundary (β := β) N‖*
          ‖(twistedIncrement N r).permMatrix ℂ-(boundaryAlternative N r).permMatrix ℂ‖ := norm_mul_le _ _
      _ ≤ 1*2 := mul_le_mul (onesBoundary_norm N) hd (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  nlinarith [show (0:ℝ) ≤ (1/4:ℝ)^N by positivity]

end
end E2.FiniteConstruction