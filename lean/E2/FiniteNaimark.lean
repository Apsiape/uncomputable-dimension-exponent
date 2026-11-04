import E2.StateConsistencyRectangular
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace E2.FiniteNaimark
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
variable {o b : Type*} [Fintype o] [DecidableEq o] [Fintype b] [DecidableEq b]

/-- All POVMs with these outcome and local index types use this same space. -/
abbrev Space (o b : Type*) := b ⊕ (o × b)

def povmIsometry (E : o → Matrix b b ℂ) : Matrix (o × b) b ℂ :=
  fun i j => QIT.psdSqrt (E i.1) i.2 j

theorem povmIsometry_isometry (E : o → Matrix b b ℂ)
    (hE : ∀ c, (E c).PosSemidef) (hsum : ∑ c, E c = 1) :
    (povmIsometry E).conjTranspose * povmIsometry E = 1 := by
  ext i j
  change (∑ k : o × b, star (QIT.psdSqrt (E k.1) k.2 i) *
    QIT.psdSqrt (E k.1) k.2 j) = (1 : Matrix b b ℂ) i j
  rw [Fintype.sum_prod_type]
  have hh c : (∑ k : b, star (QIT.psdSqrt (E c) k i) *
      QIT.psdSqrt (E c) k j) = E c i j := by
    have hm : (QIT.psdSqrt (E c)).conjTranspose * QIT.psdSqrt (E c) = E c := by
      rw [(QIT.psdSqrt_isHermitian _).eq, QIT.psdSqrt_mul_self_of_posSemidef (hE c)]
    exact congrFun (congrFun hm i) j
  simp_rw [hh]
  simpa only [Matrix.sum_apply] using congrFun (congrFun hsum i) j

def coordinate (c : o) : Matrix (o × b) (o × b) ℂ :=
  Matrix.diagonal (fun i => if i.1 = c then 1 else 0)

theorem coordinate_hermitian (c : o) :
    (coordinate (b := b) c).conjTranspose = coordinate c := by
  ext i j
  by_cases h : i = j
  · subst j; simp [coordinate, Matrix.conjTranspose_apply]
  · simp [coordinate, Matrix.conjTranspose_apply,h,Ne.symm h]

theorem coordinate_mul (c e : o) :
    coordinate (b := b) c * coordinate e = if c = e then coordinate c else 0 := by
  by_cases h : c = e
  · subst e
    simp only [coordinate, Matrix.diagonal_mul_diagonal, ite_true]
    apply congrArg Matrix.diagonal
    funext i
    by_cases hi : i.1 = c <;> simp [hi]
  · simp only [coordinate, Matrix.diagonal_mul_diagonal,h,ite_false]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i.1 = c <;> by_cases hj : i.1 = e <;> simp_all
    · simp [Matrix.diagonal_apply, hij]

theorem coordinate_sum : (∑ c : o, coordinate (b := b) c) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [coordinate, Matrix.sum_apply, Matrix.diagonal_apply]
  · simp [coordinate, Matrix.sum_apply, Matrix.diagonal_apply, h]

theorem coordinate_compression (E : o → Matrix b b ℂ)
    (hE : ∀ c, (E c).PosSemidef) (c : o) :
    (povmIsometry E).conjTranspose * coordinate c * povmIsometry E = E c := by
  have hrow : (coordinate (b := b) c * povmIsometry E : Matrix (o × b) b ℂ) =
      (fun i j => if i.1 = c then QIT.psdSqrt (E c) i.2 j else 0) := by
    ext i j
    change (Matrix.diagonal (fun i : o × b => if i.1 = c then (1:ℂ) else 0) *
      povmIsometry E) i j = _
    rw [Matrix.diagonal_mul]
    by_cases hi : i.1 = c <;> simp [povmIsometry, hi]
  rw [Matrix.mul_assoc,hrow]
  ext i j
  change (∑ k : o × b, star (QIT.psdSqrt (E k.1) k.2 i) *
      (if k.1 = c then QIT.psdSqrt (E c) k.2 j else 0)) = E c i j
  rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
  · simp only [ite_true]
    have hm : (QIT.psdSqrt (E c)).conjTranspose * QIT.psdSqrt (E c) = E c := by
      rw [(QIT.psdSqrt_isHermitian _).eq, QIT.psdSqrt_mul_self_of_posSemidef (hE c)]
    exact congrFun (congrFun hm i) j
  · intro e he hne
    simp [hne]
  · simp

/-- A reflection which carries the fixed top summand to the POVM isometry. -/
def swapIsometry (V : Matrix (o × b) b ℂ) : Matrix (Space o b) (Space o b) ℂ :=
  Matrix.fromBlocks 0 V.conjTranspose V (1 - V * V.conjTranspose)

theorem swapIsometry_hermitian (V : Matrix (o × b) b ℂ) :
    (swapIsometry V).conjTranspose = swapIsometry V := by
  simp [swapIsometry, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul]

theorem swapIsometry_square (V : Matrix (o × b) b ℂ)
    (hV : V.conjTranspose * V = 1) : swapIsometry V * swapIsometry V = 1 := by
  have hright : V.conjTranspose * (1 - V * V.conjTranspose) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]
  have hleft : (1 - V * V.conjTranspose) * V = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one, sub_self]
  have hproj : (V * V.conjTranspose) * (V * V.conjTranspose) = V * V.conjTranspose := by
    calc
      _ = V * (V.conjTranspose * V) * V.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  have hbottom : V * V.conjTranspose +
      (1 - V * V.conjTranspose) * (1 - V * V.conjTranspose) = 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hproj]
    abel
  simp only [swapIsometry, Matrix.fromBlocks_multiply, Matrix.zero_mul,
    Matrix.mul_zero, zero_add, add_zero, hV, hright, hleft, hbottom, Matrix.fromBlocks_one]

def embedding : Matrix (Space o b) b ℂ := Matrix.fromRows 1 0

theorem embedding_isometry : (embedding (o := o) (b := b)).conjTranspose * embedding (o := o) (b := b) = 1 := by
  simp [embedding, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]

def blockCoordinate (c0 c : o) : Matrix (Space o b) (Space o b) ℂ :=
  Matrix.fromBlocks (if c = c0 then 1 else 0) 0 0 (coordinate c)

def effect (E : o → Matrix b b ℂ) (c0 c : o) : Matrix (Space o b) (Space o b) ℂ :=
  swapIsometry (povmIsometry E) * blockCoordinate c0 c * swapIsometry (povmIsometry E)

theorem blockCoordinate_hermitian (c0 c : o) :
    (blockCoordinate (b := b) c0 c).conjTranspose = blockCoordinate c0 c := by
  simp only [blockCoordinate, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    coordinate_hermitian]
  split_ifs <;> simp

theorem blockCoordinate_mul (c0 c e : o) :
    blockCoordinate (b := b) c0 c * blockCoordinate c0 e =
      if c = e then blockCoordinate c0 c else 0 := by
  by_cases h : c = e
  · subst e
    simp only [blockCoordinate, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, coordinate_mul, ite_true]
    split_ifs <;> simp
  · simp only [blockCoordinate, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, coordinate_mul, h, ite_false]
    by_cases hc : c = c0 <;> by_cases he : e = c0 <;> simp_all

theorem effect_hermitian (E : o → Matrix b b ℂ) (c0 c : o) :
    (effect E c0 c).conjTranspose = effect E c0 c := by
  simp only [effect, Matrix.conjTranspose_mul, swapIsometry_hermitian,
    blockCoordinate_hermitian, Matrix.mul_assoc]

theorem effect_mul (E : o → Matrix b b ℂ)
    (hE : ∀ c, (E c).PosSemidef) (hsum : ∑ c, E c = 1) (c0 c e : o) :
    effect E c0 c * effect E c0 e = if c = e then effect E c0 c else 0 := by
  have hU := swapIsometry_square (povmIsometry E) (povmIsometry_isometry E hE hsum)
  calc
    _ = swapIsometry (povmIsometry E) * blockCoordinate c0 c *
        (swapIsometry (povmIsometry E) * swapIsometry (povmIsometry E)) *
        blockCoordinate c0 e * swapIsometry (povmIsometry E) := by simp only [Matrix.mul_assoc, effect]
    _ = swapIsometry (povmIsometry E) *
        (blockCoordinate c0 c * blockCoordinate c0 e) * swapIsometry (povmIsometry E) := by
      rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [blockCoordinate_mul]; split_ifs <;> simp [effect]

theorem blockCoordinate_sum (c0 : o) : (∑ c : o, blockCoordinate (b := b) c0 c) = 1 := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change (∑ c : o, blockCoordinate (b := b) c0 c) (.inl i) (.inl j) = _
      simp only [Matrix.sum_apply, blockCoordinate, Matrix.fromBlocks_apply₁₁]
      rw [Finset.sum_eq_single c0]
      · simp [Matrix.one_apply]
      · intro c hc hne
        simp [hne]
      · simp
    | inr j => simp [Matrix.sum_apply,blockCoordinate,Matrix.one_apply]
  | inr i =>
    cases j with
    | inl j => simp [Matrix.sum_apply,blockCoordinate,Matrix.one_apply]
    | inr j =>
      have hh := congrFun (congrFun (coordinate_sum (o := o) (b := b)) i) j
      simpa only [Matrix.sum_apply,blockCoordinate,Matrix.fromBlocks_apply₂₂,
        Matrix.one_apply,Sum.inr.injEq] using hh

theorem effect_sum (E : o → Matrix b b ℂ)
    (hE : ∀ c, (E c).PosSemidef) (hsum : ∑ c, E c = 1) (c0 : o) :
    (∑ c, effect E c0 c) = 1 := by
  simp only [effect, ← Finset.sum_mul, ← Finset.mul_sum, blockCoordinate_sum, Matrix.mul_one]
  exact swapIsometry_square _ (povmIsometry_isometry E hE hsum)

theorem effect_compression (E : o → Matrix b b ℂ)
    (hE : ∀ c, (E c).PosSemidef) (c0 c : o) :
    (embedding (o := o) (b := b)).conjTranspose * effect E c0 c * embedding = E c := by
  have hleft : (embedding (o := o) (b := b)).conjTranspose * swapIsometry (povmIsometry E) =
      Matrix.fromCols 0 (povmIsometry E).conjTranspose := by
    simp [embedding, swapIsometry, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks]
  have hright : swapIsometry (povmIsometry E) * (embedding (o := o) (b := b)) =
      Matrix.fromRows 0 (povmIsometry E) := by
    simp [embedding, swapIsometry, Matrix.fromBlocks_mul_fromRows]
  change (embedding (o := o) (b := b)).conjTranspose *
    (swapIsometry (povmIsometry E) * blockCoordinate c0 c * swapIsometry (povmIsometry E)) *
    embedding = E c
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft, Matrix.mul_assoc,
    Matrix.mul_assoc, hright]
  simp only [blockCoordinate, Matrix.fromBlocks_mul_fromRows, Matrix.mul_zero,
    Matrix.zero_mul, zero_add, add_zero, Matrix.fromCols_mul_fromRows]
  simpa only [Matrix.mul_assoc] using coordinate_compression E hE c

end
end E2.FiniteNaimark
