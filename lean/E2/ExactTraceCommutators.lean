import E2.ExactModelDefs
import Mathlib.Analysis.SpecificLimits.Normed

namespace E2.ExactTrace
noncomputable section
open scoped BigOperators Topology
variable {A : Type*} [CStarAlgebra A]

/-- Algebraic matrix units. No boundedness is imposed on a functional. -/
structure MatrixUnits (I : Type*) [DecidableEq I] where
  val : I → I → A
  adj : ∀ i j, star (val i j) = val j i
  mul : ∀ i j k l, val i j * val k l = if j=k then val i l else 0

namespace MatrixUnits
variable {I : Type*} [DecidableEq I] (u : MatrixUnits (A:=A) I)

def diagonal (s : Finset I) : A := ∑ i ∈ s, u.val i i

theorem diagonal_star (s : Finset I) : star (u.diagonal s)=u.diagonal s := by
  simp only [diagonal,star_sum,u.adj]

theorem diagonal_mul (s t : Finset I) :
    u.diagonal s*u.diagonal t=u.diagonal (s∩t) := by
  classical
  simp only [diagonal,Finset.sum_mul,Finset.mul_sum,u.mul]
  simp [Finset.sum_ite_irrel,Finset.sum_filter,Finset.inter_comm]

theorem diagonal_norm (s : Finset I) : ‖u.diagonal s‖≤1 := by
  apply IsStarProjection.norm_le
  exact ⟨by simpa [IsIdempotentElem] using u.diagonal_mul s s,u.diagonal_star s⟩

def block (s : Finset I) (f : I → I) : A := ∑ i ∈ s, u.val (f i) i

theorem block_star_mul (s t : Finset I) (f : I → I) (hf : Function.Injective f) :
    star (u.block s f)*u.block t f=u.diagonal (s∩t) := by
  classical
  simp only [block,star_sum,Finset.sum_mul,Finset.mul_sum,u.adj,u.mul,hf.eq_iff]
  simp [diagonal,Finset.sum_ite_irrel,Finset.sum_filter,Finset.inter_comm]

theorem block_mul_star (s t : Finset I) (f : I → I) (hf : Function.Injective f) :
    u.block s f*star (u.block t f)=u.diagonal ((s∩t).image f) := by
  classical
  simp only [block,star_sum,Finset.sum_mul,Finset.mul_sum,u.adj,u.mul]
  simp [diagonal,Finset.sum_ite_irrel,Finset.sum_filter,Finset.sum_image,hf.injOn,Finset.inter_comm]

theorem block_norm (s : Finset I) (f : I → I) (hf : Function.Injective f) :
    ‖u.block s f‖≤1 := by
  have h := u.diagonal_norm s
  have he := u.block_star_mul s s f hf
  simp only [Finset.inter_self] at he
  have hn := CStarRing.norm_star_mul_self (x:=u.block s f)
  rw [he] at hn
  nlinarith [norm_nonneg (u.block s f)]

end MatrixUnits

abbrev Tree := List (Fin 4)

def treeLevel : ℕ → Finset Tree
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion (fun b : Fin 4 => (treeLevel n).image (List.cons b))

theorem mem_treeLevel (w : Tree) (n : ℕ) : w∈treeLevel n ↔ w.length=n := by
  induction n generalizing w with
  | zero => simp [treeLevel]
  | succ n ih =>
    cases w with
    | nil => simp [treeLevel]
    | cons b w => simp [treeLevel,ih]

theorem treeLevel_disjoint {n m : ℕ} (h : n≠m) :
    treeLevel n∩treeLevel m=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hn,hm⟩ := Finset.mem_inter.mp hw
  exact h ((mem_treeLevel w n).mp hn |>.symm.trans ((mem_treeLevel w m).mp hm))

namespace MatrixUnits
variable (u : MatrixUnits (A:=A) Tree)

def treeBlock (n : ℕ) (b : Fin 4) : A := u.block (treeLevel n) (List.cons b)
def treeDiagonal (n : ℕ) : A := u.diagonal (treeLevel n)

theorem treeBlock_star_mul (n m : ℕ) (b : Fin 4) :
    star (u.treeBlock n b)*u.treeBlock m b=if n=m then u.treeDiagonal n else 0 := by
  rw [treeBlock,treeBlock,u.block_star_mul _ _ _ (fun _ _ h => List.cons.inj h |>.2)]
  by_cases h : n=m
  · subst m; simp [treeDiagonal]
  · simp [treeLevel_disjoint h,h,diagonal]

theorem treeBlock_mul_star (n m : ℕ) (b : Fin 4) :
    u.treeBlock n b*star (u.treeBlock m b)=
      if n=m then u.diagonal ((treeLevel n).image (List.cons b)) else 0 := by
  rw [treeBlock,treeBlock,u.block_mul_star _ _ _ (fun _ _ h => List.cons.inj h |>.2)]
  by_cases h : n=m
  · subst m; simp
  · simp [treeLevel_disjoint h,h,diagonal]

theorem treeBlock_norm (n : ℕ) (b : Fin 4) : ‖u.treeBlock n b‖≤1 :=
  u.block_norm _ _ (fun _ _ h => List.cons.inj h |>.2)

theorem treeDiagonal_norm (n : ℕ) : ‖u.treeDiagonal n‖≤1 := u.diagonal_norm _

theorem tree_children (n : ℕ) :
    (∑ b : Fin 4, u.diagonal ((treeLevel n).image (List.cons b)))=u.treeDiagonal (n+1) := by
  classical
  change _=u.diagonal (Finset.univ.biUnion (fun b : Fin 4 => (treeLevel n).image (List.cons b)))
  unfold diagonal
  symm
  apply Finset.sum_biUnion
  intro b hb c hc hbc
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  simp only [Finset.mem_image] at hw hw'
  obtain ⟨i,hi,he⟩ := hw
  obtain ⟨j,hj,hf⟩ := hw'
  have := List.cons.inj (he.trans hf.symm)
  exact hbc this.1

def weightedBlock (b : Fin 4) (n : ℕ) : A := ((1/2:ℝ)^n) • u.treeBlock n b

theorem weightedBlock_summable (b : Fin 4) : Summable (u.weightedBlock b) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).of_norm_bounded
  intro n
  simp only [weightedBlock,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤1/2) n)]
  exact mul_le_of_le_one_right (pow_nonneg (by norm_num) n) (u.treeBlock_norm n b)

def treeShift (b : Fin 4) : A := ∑' n, u.weightedBlock b n

theorem treeShift_star_mul (b : Fin 4) :
    star (u.treeShift b)*u.treeShift b=∑' n, ((1/4:ℝ)^n) • u.treeDiagonal n := by
  unfold treeShift
  rw [tsum_star,←(u.weightedBlock_summable b).star.tsum_mul_right]
  apply tsum_congr
  intro n
  rw [←(u.weightedBlock_summable b).tsum_mul_left]
  rw [tsum_eq_single n]
  · simp only [weightedBlock,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,
      smul_smul,u.treeBlock_star_mul,ite_true]
    congr 1
    rw [←mul_pow]; norm_num
  · intro m hm
    simp [weightedBlock,star_smul,smul_mul_assoc,mul_smul_comm,u.treeBlock_star_mul,hm.symm]

theorem treeShift_mul_star (b : Fin 4) :
    u.treeShift b*star (u.treeShift b)=∑' n, ((1/4:ℝ)^n) •
      u.diagonal ((treeLevel n).image (List.cons b)) := by
  unfold treeShift
  rw [tsum_star,←(u.weightedBlock_summable b).tsum_mul_right]
  apply tsum_congr
  intro n
  rw [←(u.weightedBlock_summable b).star.tsum_mul_left]
  rw [tsum_eq_single n]
  · simp only [weightedBlock,star_smul,star_trivial,smul_mul_assoc,mul_smul_comm,
      smul_smul,u.treeBlock_mul_star,ite_true]
    congr 1
    rw [←mul_pow]; norm_num
  · intro m hm
    simp [weightedBlock,star_smul,smul_mul_assoc,mul_smul_comm,u.treeBlock_mul_star,hm.symm]

theorem geometric_diagonal_summable (s : ℕ → Finset Tree) :
    Summable (fun n => ((1/4:ℝ)^n) • u.diagonal (s n)) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).of_norm_bounded
  intro n
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤1/4) n)]
  exact mul_le_of_le_one_right (pow_nonneg (by norm_num) n) (u.diagonal_norm _)

/-- Four compact weighted shifts give a finite commutator certificate. -/
theorem tree_commutators :
    (∑ b : Fin 4, (star (u.treeShift b)*u.treeShift b-u.treeShift b*star (u.treeShift b)))=
      (4:ℝ) • u.val [] [] := by
  let D : A := ∑' n, ((1/4:ℝ)^n) • u.treeDiagonal n
  let R : A := ∑' n, ((1/4:ℝ)^n) • u.treeDiagonal (n+1)
  have hD : D=u.treeDiagonal 0+(1/4:ℝ) • R := by
    dsimp [D,R]
    simp only [treeDiagonal]
    rw [(u.geometric_diagonal_summable treeLevel).tsum_eq_zero_add]
    simp only [pow_zero,one_smul]
    congr 1
    rw [←(u.geometric_diagonal_summable (fun n => treeLevel (n+1))).tsum_const_smul]
    apply tsum_congr
    intro n
    simp only [pow_succ,smul_smul,mul_comm]
  have hR : (∑ b : Fin 4, u.treeShift b*star (u.treeShift b))=R := by
    simp only [u.treeShift_mul_star]
    rw [←Summable.tsum_finsetSum]
    · apply tsum_congr
      intro n
      rw [←Finset.smul_sum,u.tree_children]
    · intro b hb
      exact u.geometric_diagonal_summable (fun n => (treeLevel n).image (List.cons b))
  rw [Finset.sum_sub_distrib,hR]
  simp only [u.treeShift_star_mul]
  change (∑ _b : Fin 4, D)-R=_
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [hD]
  have h0 : u.treeDiagonal 0=u.val [] [] := by simp [treeDiagonal,treeLevel,diagonal]
  rw [h0]
  simp only [nsmul_eq_mul,←Nat.cast_smul_eq_nsmul ℝ]
  module

/-- Every algebraic complex trace kills a matrix-unit diagonal with infinitely
many equivalent orthogonal copies. Its continuity is not needed. -/
theorem trace_root_zero (φ : A →ₗ[ℂ] ℂ) (hφ : ∀ a b, φ (a*b)=φ (b*a)) :
    φ (u.val [] [])=0 := by
  have h := congrArg φ u.tree_commutators
  have hz : φ (∑ b : Fin 4, (star (u.treeShift b)*u.treeShift b-u.treeShift b*star (u.treeShift b)))=0 := by
    simp only [map_sum,map_sub,hφ]
    simp
  rw [hz] at h
  have hs : (4:ℝ) • u.val [] []=(4:ℂ) • u.val [] [] :=
    (IsScalarTower.algebraMap_smul ℂ (4:ℝ) (u.val [] [])).symm
  rw [hs,map_smul] at h
  simpa using (smul_eq_zero.mp h.symm).resolve_left (by norm_num : (4:ℂ)≠0)

end MatrixUnits

/-- Countably many orthogonal equivalent ranges kill their common source in
any complex-linear cyclic functional. -/
theorem orthogonal_copies_trace_zero (φ : A →ₗ[ℂ] ℂ)
    (hφ : ∀ a b, φ (a*b)=φ (b*a)) (e : A) (v : ℕ → A)
    (hve : ∀ i, v i*e=v i)
    (hvv : ∀ i j, star (v i)*v j=if i=j then e else 0) : φ e=0 := by
  classical
  let u : MatrixUnits (A:=A) Tree := {
    val := fun i j => v (Encodable.encode i)*star (v (Encodable.encode j))
    adj := by intro i j; simp only [star_mul,star_star]
    mul := by
      intro i j k l
      simp only [mul_assoc,←mul_assoc (star (v (Encodable.encode j))) (v (Encodable.encode k)),hvv]
      by_cases h : j=k
      · subst k
        simp only [ite_true,←mul_assoc,hve]
      · have he : Encodable.encode j≠Encodable.encode k := fun he => h (Encodable.encode_injective he)
        simp [he,h] }
  have hz := u.trace_root_zero φ hφ
  change φ (v (Encodable.encode ([]:Tree))*star (v (Encodable.encode ([]:Tree))))=0 at hz
  rw [hφ,hvv] at hz
  simpa using hz

end
end E2.ExactTrace
