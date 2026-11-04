import E2.FiniteSourceTimeGuard
import E2.FiniteSourceDressing

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def addressGaugeBasis (p : CounterProgram) (N k : ℕ) :
    SourceBasis N k ≃ BinaryWord N × (Bits k × (BinaryWord N × BinaryWord N)) :=
  (addressLift (addressDressing p N k).symm).trans (Equiv.prodAssoc _ _ _)

def addressBoundary (p : CounterProgram) (N k : ℕ) : Equiv.Perm (Bits k) :=
  ((rotateWord k).symm)^flagPrefix (finiteMask p N) (2^N)

theorem addressGauge_forward (p : CounterProgram) (N k : ℕ) :
    (addressGaugeBasis p N k).symm.trans
      ((addressLift (addressForward p N k)).trans (addressGaugeBasis p N k)) =
    twistedIncrement N ((addressBoundary p N k).prodCongr (Equiv.refl (BinaryWord N × BinaryWord N))) := by
  apply Equiv.ext
  rintro ⟨a,b,q,t⟩
  have hh := congrArg (fun s : Equiv.Perm (BinaryWord N × Bits k) => s (a,b))
    (address_dressed_increment p N k)
  simp only [Equiv.trans_apply] at hh
  change (fun z : BinaryWord N × Bits k => (z.1,(z.2,(q,t))))
    ((addressDressing p N k).symm (addressForward p N k (addressDressing p N k (a,b)))) = _
  rw [hh]
  cases hall : a.val.all id <;>
    simp only [twistedIncrement,skewShift,Equiv.coe_fn_mk,hall,eq_self,Bool.false_eq_true,
      ite_true,ite_false,zpow_zero,zpow_one,Equiv.Perm.one_apply,addressBoundary,
      Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply]

theorem source_address_guard_norm (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    ‖(sourceCore p N 12-sourceCore p N 3*((1-sourceCore p N 1)+
      sourceCore p N 2*sourceCore p N 12*(sourceCore p N 2).conjTranspose*sourceCore p N 1))*
        (1-sourceCore p N 0)‖ ≤ 2*(1/4:ℝ)^N := by
  let k := finiteSlots p N
  let g := addressGaugeBasis p N k
  let e := (sourceBasisEquiv N k).trans g
  let φ := matrixReindexStar e
  let r := (addressBoundary p N k).prodCongr (Equiv.refl (BinaryWord N × BinaryWord N))
  have hA : φ (sourceCore p N 0)=rawWordCoordinate N := by
    rw [show sourceCore p N 0=sourceDiagonal N k (fun z => listCoordinate z.1.1.val) from rfl,
      sourceDiagonal_reindex]
    rfl
  have hP : φ (sourceCore p N 1)=rawWordDigit N := by
    rw [show sourceCore p N 1=sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false)) from rfl,
      sourceDiagonal_reindex]
    rfl
  have hT : φ (sourceCore p N 2)=(rawWordRotation N).permMatrix ℂ := by
    rw [show sourceCore p N 2=(sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ from rfl,
      sourcePermutation_reindex]
    congr 1
    apply Equiv.ext
    rintro ⟨a,b,q,t⟩
    simp [g,addressGaugeBasis,addressLift,addressRotation,rawWordRotation]
  have hX : φ (sourceCore p N 3)=(rawWordFlip N).permMatrix ℂ := by
    rw [show sourceCore p N 3=(sourcePerm N k (addressLift (addressFlip p N k))).permMatrix ℂ from rfl,
      sourcePermutation_reindex]
    congr 1
    apply Equiv.ext
    rintro ⟨a,b,q,t⟩
    simp [g,addressGaugeBasis,addressLift,addressFlip,rawWordFlip]
  have hV : φ (sourceCore p N 12)=((twistedIncrement N r).permMatrix ℂ).conjTranspose := by
    rw [show sourceCore p N 12=(sourcePerm N k (addressLift (addressForward p N k).symm)).permMatrix ℂ from rfl,
      sourcePermutation_reindex,Matrix.conjTranspose_permMatrix]
    have hv := congrArg Equiv.symm (addressGauge_forward p N k)
    exact congrArg (fun s : Equiv.Perm (BinaryWord N × (Bits k × (BinaryWord N × BinaryWord N))) => s.permMatrix ℂ) hv
  have hs (M : Mat (2^(3*N+k))) : φ M.conjTranspose=(φ M).conjTranspose := map_star φ M
  rw [←matrixReindex_norm e]
  change ‖φ _‖≤_
  simp only [map_mul,map_sub,map_add,map_one,hs,hA,hP,hT,hX,hV]
  exact raw_original_guard_norm N hN r

/-- Operator bound for the unchanged original dressed address guard. -/
theorem source_address_guard_op_defect (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    ‖Poly.eval (sourceTuple p N)
      (guardRelation (sv p 0) (sv p 1) (sv p 2) (sv p 3) (sv p 12))‖ ≤ 2*(1/4:ℝ)^N := by
  simpa only [guardRelation,conjP,Poly.eval_mul,Poly.eval_sub,Poly.eval_add,Poly.eval_adj,Poly.eval_one,
    sourceTuple_core p N 0 (by omega),sourceTuple_core p N 1 (by omega),
    sourceTuple_core p N 2 (by omega),sourceTuple_core p N 3 (by omega),
    sourceTuple_core p N 12 (by omega)] using source_address_guard_norm p N hN

end
end E2.FiniteConstruction