import E2.FiniteGuardTransport

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def timeBasisEquiv (N k : ℕ) : SourceBasis N k ≃ BinaryWord N × ((BinaryWord N × Bits k) × BinaryWord N) where
  toFun z := (z.2.2,(z.1,z.2.1))
  invFun z := (z.2.1,(z.2.2,z.1))
  left_inv z := by rcases z with ⟨⟨a,b⟩,q,t⟩; rfl
  right_inv z := by rcases z with ⟨t,⟨a,b⟩,q⟩; rfl

theorem sourceDiagonal_reindex {β : Type*} [Fintype β] [DecidableEq β]
    (N k : ℕ) (e : SourceBasis N k ≃ β) (v : SourceBasis N k → ℝ) :
    matrixReindexStar ((sourceBasisEquiv N k).trans e) (sourceDiagonal N k v)=
      Matrix.diagonal (fun z => (v (e.symm z):ℂ)) := by
  rw [sourceDiagonal,matrixReindex_diagonal]
  congr 1
  funext z
  simp

theorem sourcePermutation_reindex {β : Type*} [Fintype β] [DecidableEq β]
    (N k : ℕ) (e : SourceBasis N k ≃ β) (s : Equiv.Perm (SourceBasis N k)) :
    matrixReindexStar ((sourceBasisEquiv N k).trans e) ((sourcePerm N k s).permMatrix ℂ)=
      Equiv.Perm.permMatrix ℂ (e.symm.trans (s.trans e)) := by
  rw [matrixReindex_permutation]
  congr 1
  apply Equiv.ext
  intro z
  simp [sourcePerm]

theorem twistedIncrement_refl {β : Type*} (N : ℕ) :
    twistedIncrement N (Equiv.refl β)=(incrementWord N).prodCongr (Equiv.refl β) := by
  apply Equiv.ext
  rintro ⟨a,b⟩
  change (incrementWord N a,((Equiv.refl β : Equiv.Perm β) ^
    (if a.val.all id then 1 else 0 : ℤ)) b)=(incrementWord N a,b)
  rw [show (Equiv.refl β : Equiv.Perm β)=1 from rfl]
  simp

theorem source_time_guard_norm (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    ‖(sourceCore p N 13-sourceCore p N 11*((1-sourceCore p N 9)+
      sourceCore p N 10*sourceCore p N 13*(sourceCore p N 10).conjTranspose*sourceCore p N 9))*
        (1-sourceCore p N 8)‖ ≤ 2*(1/4:ℝ)^N := by
  let k := finiteSlots p N
  let e := (sourceBasisEquiv N k).trans (timeBasisEquiv N k)
  let φ := matrixReindexStar e
  have hA : φ (sourceCore p N 8)=rawWordCoordinate N := by
    rw [show sourceCore p N 8=sourceDiagonal N k (fun z => listCoordinate z.2.2.val) from rfl,
      sourceDiagonal_reindex]
    rfl
  have hP : φ (sourceCore p N 9)=rawWordDigit N := by
    rw [show sourceCore p N 9=sourceDiagonal N k (fun z => boolValue (z.2.2.val.headD false)) from rfl,
      sourceDiagonal_reindex]
    rfl
  have hT : φ (sourceCore p N 10)=(rawWordRotation N).permMatrix ℂ := by
    rw [show sourceCore p N 10=(sourcePerm N k (timeLift (rotateBinary N))).permMatrix ℂ from rfl,
      sourcePermutation_reindex]
    congr 1
  have hX : φ (sourceCore p N 11)=(rawWordFlip N).permMatrix ℂ := by
    rw [show sourceCore p N 11=(sourcePerm N k (timeLift (flipFirstWord N))).permMatrix ℂ from rfl,
      sourcePermutation_reindex]
    congr 1
  have hU : φ (sourceCore p N 13)=
      ((twistedIncrement N (Equiv.refl ((BinaryWord N × Bits k) × BinaryWord N))).permMatrix ℂ).conjTranspose := by
    rw [show sourceCore p N 13=(sourcePerm N k (timeLift (incrementWord N).symm)).permMatrix ℂ from rfl,
      sourcePermutation_reindex,twistedIncrement_refl,Matrix.conjTranspose_permMatrix]
    congr 1
  have hs (M : Mat (2^(3*N+k))) : φ M.conjTranspose=(φ M).conjTranspose := map_star φ M
  rw [←matrixReindex_norm e]
  change ‖φ _‖≤_
  simp only [map_mul,map_sub,map_add,map_one,hs,hA,hP,hT,hX,hU]
  exact raw_original_guard_norm N hN (Equiv.refl ((BinaryWord N × Bits k) × BinaryWord N))

/-- Operator bound for the unchanged original guarded time increment. -/
theorem source_time_guard_op_defect (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    ‖Poly.eval (sourceTuple p N)
      (guardRelation (sv p 8) (sv p 9) (sv p 10) (sv p 11) (sv p 13))‖ ≤ 2*(1/4:ℝ)^N := by
  simpa only [guardRelation,conjP,Poly.eval_mul,Poly.eval_sub,Poly.eval_add,Poly.eval_adj,Poly.eval_one,
    sourceTuple_core p N 8 (by omega),sourceTuple_core p N 9 (by omega),
    sourceTuple_core p N 10 (by omega),sourceTuple_core p N 11 (by omega),
    sourceTuple_core p N 13 (by omega)] using source_time_guard_norm p N hN

end
end E2.FiniteConstruction