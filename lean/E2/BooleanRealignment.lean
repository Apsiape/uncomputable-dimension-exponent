import E2.BooleanMixedAmplitude
import E2.BooleanExtractionPVM

namespace E2.BooleanRealignment
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
open Companion.Analytic BooleanMixedAmplitude
variable {a d : ℕ}

abbrev refSize (a d : ℕ) := Fintype.card (Reference a d)

def lift (X : Mat a) : Mat (refSize a d) :=
  Matrix.reindex (referenceEquiv a d) (referenceEquiv a d)
    (Matrix.kroneckerMap (fun x y : ℂ => x*y) X.transpose (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))

theorem lift_one : lift (d := d) (1 : Mat a) = 1 := by
  simp [lift, Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem lift_mul (X Y : Mat a) : lift (d := d) (X*Y) = lift Y * lift X := by
  simp only [lift, Matrix.transpose_mul]
  have hk : Matrix.kroneckerMap (fun x y : ℂ => x*y) (Y.transpose * X.transpose)
      (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) =
      Matrix.kroneckerMap (fun x y : ℂ => x*y) Y.transpose 1 * Matrix.kroneckerMap (fun x y : ℂ => x*y) X.transpose 1 := by
    erw [← Matrix.mul_kronecker_mul]
    rw [Matrix.one_mul]
  rw [hk]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (referenceEquiv a d)).map_mul _ _

theorem lift_hermitian (X : Mat a) (hX : X.conjTranspose = X) :
    (lift (d := d) X).conjTranspose = lift X := by
  simp only [lift, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
  congr 1
  erw [Matrix.conjTranspose_kronecker]
  rw [Matrix.conjTranspose_one, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,hX]

theorem realign_bob (R : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (Y : Mat d) :
    realign (Matrix.kroneckerMap (fun x y : ℂ => x*y) (1 : Mat a) Y * R) = Y * realign R := by
  ext i j
  simp [realign, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, mul_ite]

theorem realign_alice (R : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) (X : Mat a) :
    realign (Matrix.kroneckerMap (fun x y : ℂ => x*y) X (1 : Mat d) * R) = realign R * lift X := by
  ext i j
  change (∑ k : Fin a × Fin d, (Matrix.kroneckerMap (fun x y : ℂ => x*y) X (1 : Mat d))
      (((referenceEquiv a d).symm j).1,i) k * R k (((referenceEquiv a d).symm j).2)) =
    ∑ k, R (((referenceEquiv a d).symm k).1,i) (((referenceEquiv a d).symm k).2) *
      (Matrix.kroneckerMap (fun x y : ℂ => x*y) X.transpose (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))
        ((referenceEquiv a d).symm k) ((referenceEquiv a d).symm j)
  have he := (referenceEquiv a d).symm.sum_comp (fun z : Reference a d =>
    R (z.1,i) z.2 *
      (Matrix.kroneckerMap (fun x y : ℂ => x*y) X.transpose
        (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)) z ((referenceEquiv a d).symm j))
  rw [he]
  simp [Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.transpose_apply, mul_ite, ite_mul, mul_comm]

theorem realign_sub (R S : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    realign (R-S) = realign R - realign S := rfl

theorem realign_squared (R : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) :
    hsSquared (realign R) = hsSquared R := by
  change (∑ i : Fin d, ∑ j, Complex.normSq
    (R (((referenceEquiv a d).symm j).1,i) (((referenceEquiv a d).symm j).2))) = _
  have he (i : Fin d) : (∑ j, Complex.normSq
    (R (((referenceEquiv a d).symm j).1,i) (((referenceEquiv a d).symm j).2))) =
      ∑ z : Reference a d, Complex.normSq (R (z.1,i) z.2) := by
    exact (referenceEquiv a d).symm.sum_comp (fun z : Reference a d => Complex.normSq (R (z.1,i) z.2))
  simp_rw [he]
  simp only [hsSquared,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem consistency_squared (ρ : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hρ : ρ.PosSemidef) (ht : Matrix.trace ρ = 1)
    (X : Mat a) (Y : Mat d)
    (hX : Domain.reflection.Holds X) (hY : Domain.reflection.Holds Y) :
    hs (Y * amplitude ρ - amplitude ρ * lift X)^2 =
      2 - 2 * (Matrix.trace (ρ * Matrix.kroneckerMap (fun x y : ℂ => x*y) X Y)).re := by
  let R := QIT.psdSqrt ρ
  let L := Matrix.kroneckerMap (fun x y : ℂ => x*y) (1 : Mat a) Y - Matrix.kroneckerMap (fun x y : ℂ => x*y) X (1 : Mat d)
  have hR : R * R.conjTranspose = ρ := by
    dsimp [R]
    rw [(QIT.psdSqrt_isHermitian ρ).eq, QIT.psdSqrt_mul_self_of_posSemidef hρ]
  have hL : L.conjTranspose = L := by
    simp [L, Matrix.conjTranspose_kronecker, hX.1, hY.1]
  have hsq : L*L = (2:ℂ) • (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ) -
      (2:ℂ) • Matrix.kroneckerMap (fun x y : ℂ => x*y) X Y := by
    dsimp only [L]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    erw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [Matrix.one_mul,Matrix.one_mul,Matrix.mul_one,Matrix.mul_one,
      Matrix.mul_one,hX.2,hY.2,Matrix.one_kronecker_one]
    simp only [Matrix.one_mul]
    module
  have he : Y * amplitude ρ - amplitude ρ * lift X = realign (L*R) := by
    dsimp only [L]
    rw [Matrix.sub_mul, realign_sub, realign_bob, realign_alice]
    rfl
  rw [he, hs, hsNorm_sq, realign_squared, hsSquared_trace,
    Matrix.conjTranspose_mul, hL]
  have hcycle : Matrix.trace (R.conjTranspose * L * (L*R)) =
      Matrix.trace (ρ * (L*L)) := by
    calc
      _ = Matrix.trace (R.conjTranspose * ((L*L)*R)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((L*L)*R) * R.conjTranspose) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((L*L)*ρ) := by rw [Matrix.mul_assoc,hR]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [hcycle,hsq]
  simp [Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,ht]

end
end E2.BooleanRealignment
