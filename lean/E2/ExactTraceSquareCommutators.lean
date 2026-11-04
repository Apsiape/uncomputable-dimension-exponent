import E2.ExactTraceCommutators
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

namespace E2.ExactTrace
noncomputable section
open scoped BigOperators Topology
variable {A : Type*} [CStarAlgebra A]

/-- Matrix-shaped square roots; the diagonal need not consist of projections. -/
structure OrthogonalSquares (I : Type*) [DecidableEq I] where
  val : I → I → A
  square : I → I → A
  adj : ∀ i j, star (val i j)=val j i
  mul : ∀ i j k l, val i j*val k l=if j=k then square i l else 0
  square_adj : ∀ i, IsSelfAdjoint (square i i)
  square_orthogonal : ∀ i j, i≠j → square i i*square j j=0
  square_norm : ∀ i, ‖square i i‖≤1

namespace OrthogonalSquares
variable {I : Type*} [DecidableEq I] (u : OrthogonalSquares (A:=A) I)

def diagonal (s : Finset I) : A := ∑ i ∈ s, u.square i i

theorem diagonal_norm (s : Finset I) : ‖u.diagonal s‖≤1 := by
  have he := IsSelfAdjoint.nnnorm_sum_eq_sup s
    (fun i hi => u.square_adj i) (fun i j hij => u.square_orthogonal i j hij)
  have hn : ‖u.diagonal s‖₊≤1 := by
    change ‖∑ i ∈ s, u.square i i‖₊≤1
    rw [he]
    exact Finset.sup_le (fun i hi => by exact_mod_cast u.square_norm i)
  exact_mod_cast hn

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

end OrthogonalSquares

namespace OrthogonalSquares
variable (u : OrthogonalSquares (A:=A) Tree)

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
      (4:ℝ) • u.square [] [] := by
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
  have h0 : u.treeDiagonal 0=u.square [] [] := by simp [treeDiagonal,treeLevel,diagonal]
  rw [h0]
  simp only [nsmul_eq_mul,←Nat.cast_smul_eq_nsmul ℝ]
  module

/-- Every algebraic complex trace kills a matrix-unit diagonal with infinitely
many equivalent orthogonal copies. Its continuity is not needed. -/
theorem trace_root_zero (φ : A →ₗ[ℂ] ℂ) (hφ : ∀ a b, φ (a*b)=φ (b*a)) :
    φ (u.square [] [])=0 := by
  have h := congrArg φ u.tree_commutators
  have hz : φ (∑ b : Fin 4, (star (u.treeShift b)*u.treeShift b-u.treeShift b*star (u.treeShift b)))=0 := by
    simp only [map_sum,map_sub,hφ]
    simp
  rw [hz] at h
  have hs : (4:ℝ) • u.square [] []=(4:ℂ) • u.square [] [] :=
    (IsScalarTower.algebraMap_smul ℂ (4:ℝ) (u.square [] [])).symm
  rw [hs,map_smul] at h
  simpa using (smul_eq_zero.mp h.symm).resolve_left (by norm_num : (4:ℂ)≠0)

end OrthogonalSquares
/-- Cyclic functionals kill the square of a self-adjoint contraction with
countably many orthogonal unitary copies. -/
theorem orthogonal_square_trace_zero (φ : A →ₗ[ℂ] ℂ)
    (hφ : ∀ a b, φ (a*b)=φ (b*a)) (b : A) (hb : IsSelfAdjoint b) (hbn : ‖b‖≤1)
    (x : ℕ → A) (hx : ∀ i, star (x i)=x i ∧ x i*x i=1)
    (horth : ∀ i j, i≠j → b*x i*x j*b=0) : φ (b*b)=0 := by
  classical
  let X : Tree → A := fun i => x (Encodable.encode i)
  have hX (i : Tree) : star (X i)=X i ∧ X i*X i=1 := hx _
  have hO (i j : Tree) (hij : i≠j) : b*X i*X j*b=0 :=
    horth _ _ (fun h => hij (Encodable.encode_injective h))
  let u : OrthogonalSquares (A:=A) Tree := {
    val := fun i j => X i*b*X j
    square := fun i j => X i*(b*b)*X j
    adj := by intro i j; simp only [star_mul,(hX i).1,(hX j).1,hb.star_eq,mul_assoc]
    mul := by
      intro i j k l
      calc
        _ = X i*(b*X j*X k*b)*X l := by simp only [mul_assoc]
        _ = _ := by
          by_cases h : j=k
          · subst k
            simp only [ite_true,mul_assoc,←mul_assoc (X j) (X j),(hX j).2,one_mul]
          · rw [hO j k h,if_neg h,mul_zero,zero_mul]
    square_adj := by
      intro i
      change star (X i*(b*b)*X i)=X i*(b*b)*X i
      simp only [star_mul,(hX i).1,hb.star_eq,mul_assoc]
    square_orthogonal := by
      intro i j hij
      calc
        _ = X i*b*(b*X i*X j*b)*b*X j := by simp only [mul_assoc]
        _ = 0 := by rw [hO i j hij,mul_zero,zero_mul,zero_mul]
    square_norm := by
      intro i
      let U : unitary A := ⟨X i,⟨by rw [(hX i).1,(hX i).2],by rw [(hX i).1,(hX i).2]⟩⟩
      change ‖(U:A)*(b*b)*(U:A)‖≤1
      rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
      have hn := norm_mul_le b b
      nlinarith [norm_nonneg b] }
  have hz := u.trace_root_zero φ hφ
  change φ (X []*(b*b)*X [])=0 at hz
  have he : φ (X []*(b*b)*X [])=φ (b*b) := by
    rw [mul_assoc,hφ, mul_assoc,(hX []).2,mul_one]
  rwa [he] at hz

end
end E2.ExactTrace
