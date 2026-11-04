import E2.FiniteSourceDomains
import E2.PolyEval

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem sourceTuple_core (p : CounterProgram) (N n : ℕ) (hn : n<23) :
    Poly.eval (sourceTuple p N) (sv p n)=sourceCore p N n := by
  have hsize : n<sourceSize p := by unfold sourceSize; omega
  simp only [sv,Poly.eval_var,sourceTuple,Fin.val_mk,Nat.mod_eq_of_lt hsize,hn,↓reduceDIte]

theorem sourcePerm_symm (N k : ℕ) (s : Equiv.Perm (SourceBasis N k)) :
    (sourcePerm N k s).symm=sourcePerm N k s.symm := by
  apply Equiv.ext
  intro i
  rfl

theorem source_carry_matrix (p : CounterProgram) (N : ℕ) :
    (sourceCore p N 12).conjTranspose*sourceCore p N 0*sourceCore p N 12-
      (sourceCore p N 0-1+(7/4:ℂ) • sourceCore p N 14) =
    sourceDiagonal N (finiteSlots p N) (fun z =>
      if z.1.1.val.all id then (1/4:ℝ)^N else 0) := by
  let k := finiteSlots p N
  let σ := sourcePerm N k (addressLift (addressForward p N k).symm)
  have hs : σ.symm=sourcePerm N k (addressLift (addressForward p N k)) := by
    apply Equiv.ext
    intro i
    rfl
  have hc := perm_conj_diagonal σ.symm
    (fun i => (listCoordinate (sourceBasisEquiv N k i).1.1.val:ℂ))
  simp only [Matrix.conjTranspose_permMatrix,inv_inv] at hc
  change ((Equiv.Perm.permMatrix ℂ σ.symm))*sourceCore p N 0*(σ.permMatrix ℂ)=_ at hc
  change (σ.permMatrix ℂ).conjTranspose*sourceCore p N 0*(σ.permMatrix ℂ)-
    (sourceCore p N 0-1+(7/4:ℂ) • sourceCore p N 14)=_
  rw [Matrix.conjTranspose_permMatrix]
  change (Equiv.Perm.permMatrix ℂ σ.symm)*sourceCore p N 0*σ.permMatrix ℂ-_=_
  rw [hc]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [sourceCore,sourceDiagonal,Matrix.sub_apply,Matrix.add_apply,
      Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq]
    have hb : (sourceBasisEquiv N k (σ.symm i)).1.1 =
        incrementWord N (sourceBasisEquiv N k i).1.1 := by
      rw [hs,sourcePerm_basis]
      rfl
    change (listCoordinate (sourceBasisEquiv N k (σ.symm i)).1.1.val:ℂ)-
      ((listCoordinate (sourceBasisEquiv N k i).1.1.val:ℂ)-1+
        (7/4:ℂ)*(listCarry (sourceBasisEquiv N k i).1.1.val:ℂ)) = _
    rw [hb]
    have h := listIncrement_coordinate (sourceBasisEquiv N k i).1.1.val
    rw [(sourceBasisEquiv N k i).1.1.property] at h
    have he : listCoordinate (listIncrement (sourceBasisEquiv N k i).1.1.val)-
        (listCoordinate (sourceBasisEquiv N k i).1.1.val-1+
          (7/4:ℝ)*listCarry (sourceBasisEquiv N k i).1.1.val) =
        if (sourceBasisEquiv N k i).1.1.val.all id then (1/4:ℝ)^N else 0 := by linarith
    have heC := congrArg (fun x : ℝ => (x:ℂ)) he
    push_cast at heC
    have hiv : (incrementWord N (sourceBasisEquiv N k i).1.1).val =
        listIncrement (sourceBasisEquiv N k i).1.1.val := rfl
    rw [hiv]
    push_cast
    simpa only [k] using heC
  · simp [sourceCore,sourceDiagonal,Matrix.diagonal_apply,hij]

/-- The carry-step bound for the unchanged original source polynomial. -/
theorem source_carry_op_defect (p : CounterProgram) (N : ℕ) :
    ‖Poly.eval (sourceTuple p N)
      (conjP (sv p 12).adj (sv p 0)-
        (sv p 0-1+Poly.const (7/4)*sv p 14))‖ ≤ (1/4:ℝ)^N := by
  have he : Poly.eval (sourceTuple p N)
      (conjP (sv p 12).adj (sv p 0)-
        (sv p 0-1+Poly.const (7/4)*sv p 14)) =
      (sourceCore p N 12).conjTranspose*sourceCore p N 0*sourceCore p N 12-
        (sourceCore p N 0-1+(7/4:ℂ) • sourceCore p N 14) := by
    simp only [conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_adj,Poly.eval_one,
      Poly.eval_add,Poly.eval_const,sourceTuple_core p N 12 (by omega),
      sourceTuple_core p N 0 (by omega),sourceTuple_core p N 14 (by omega),
      Matrix.conjTranspose_conjTranspose,Matrix.smul_mul,Matrix.one_mul]
    norm_num
  rw [he,source_carry_matrix,sourceDiagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  cases h : (sourceBasisEquiv N (finiteSlots p N) i).1.1.val.all id <;>
    simp [h,abs_of_nonneg (by positivity : (0:ℝ)≤(1/4:ℝ)^N)]

end
end E2.FiniteConstruction