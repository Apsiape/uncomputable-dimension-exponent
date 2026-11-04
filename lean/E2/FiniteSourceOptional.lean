import E2.FinitePermutationTransport
import E2.FiniteSourceCoordinates

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

instance finiteSlotsNeZero (p : CounterProgram) (N : ℕ) : NeZero (finiteSlots p N) :=
  ⟨Nat.ne_of_gt (finiteSlots_pos p N)⟩

def sourceOptionalRead (p : CounterProgram) (N : ℕ) (i : Fin (2^(3*N+finiteSlots p N))) :
    BinaryWord N × Bits (finiteSlots p N) := (sourceBasisEquiv N (finiteSlots p N) i).1

def sourceOptionalShift (p : CounterProgram) (N : ℕ) : Equiv.Perm (Fin (2^(3*N+finiteSlots p N))) :=
  sourcePerm N (finiteSlots p N) (addressLift (addressForward p N (finiteSlots p N)).symm)

def sourceOptionalFlip (p : CounterProgram) (N : ℕ) : Equiv.Perm (Fin (2^(3*N+finiteSlots p N))) :=
  sourcePerm N (finiteSlots p N) (addressLift (optionalFlip (wordMask p N)))

theorem sourceOptionalShift_read (p : CounterProgram) (N : ℕ) (i : Fin (2^(3*N+finiteSlots p N))) :
    sourceOptionalRead p N (sourceOptionalShift p N i) =
      optionalBackward (incrementWord N) (wordMask p N) (sourceOptionalRead p N i) := by
  unfold sourceOptionalRead sourceOptionalShift
  rw [sourcePerm_basis]
  rfl

theorem sourceOptionalFlip_read (p : CounterProgram) (N : ℕ) (i : Fin (2^(3*N+finiteSlots p N))) :
    sourceOptionalRead p N (sourceOptionalFlip p N i) =
      optionalFlip (wordMask p N) (sourceOptionalRead p N i) := by
  unfold sourceOptionalRead sourceOptionalFlip
  rw [sourcePerm_basis]
  rfl

theorem source_optional_B (p : CounterProgram) (N : ℕ) :
    sourceCore p N 19=seriesMatrix (sourceOptionalShift p N)
      (fun i => optionalDigit (wordMask p N) (sourceOptionalRead p N i)) := by
  change Matrix.diagonal _=Matrix.diagonal _
  congr 1
  funext i
  congr 1
  exact (permutationSeries_map _ _ _ (sourceOptionalShift_read p N) _ i).symm

theorem source_optional_C (p : CounterProgram) (N : ℕ) :
    sourceCore p N 20=seriesMatrix (sourceOptionalShift p N)
      (fun i => optionalFlag (wordMask p N) (sourceOptionalRead p N i)) := by
  change Matrix.diagonal _=Matrix.diagonal _
  congr 1
  funext i
  congr 1
  exact (permutationSeries_map _ _ _ (sourceOptionalShift_read p N) _ i).symm

theorem source_optional_affine_B (p : CounterProgram) (N : ℕ) :
    sourceCore p N 12*sourceCore p N 19*(sourceCore p N 12).conjTranspose =
      (4:ℂ) • sourceCore p N 19-(3:ℂ) • sourceCore p N 21 := by
  rw [source_optional_B]
  exact seriesMatrix_affine _ _ (fun i => optionalDigit_bounds _ _)

theorem source_optional_affine_C (p : CounterProgram) (N : ℕ) :
    sourceCore p N 12*sourceCore p N 20*(sourceCore p N 12).conjTranspose =
      (4:ℂ) • sourceCore p N 20-(3:ℂ) • sourceCore p N 18 := by
  rw [source_optional_C]
  exact seriesMatrix_affine _ _ (fun i => optionalFlag_bounds _ _)

theorem source_optional_tail_norm (p : CounterProgram) (N : ℕ) :
    ‖sourceCore p N 22*(sourceCore p N 12*sourceCore p N 19*(sourceCore p N 12).conjTranspose)-
      (sourceCore p N 12*sourceCore p N 19*(sourceCore p N 12).conjTranspose)*sourceCore p N 22‖ ≤
      (1/4:ℝ)^N := by
  change ‖(sourceOptionalFlip p N).permMatrix ℂ*
    ((sourceOptionalShift p N).permMatrix ℂ*sourceCore p N 19*((sourceOptionalShift p N).permMatrix ℂ).conjTranspose)-
    ((sourceOptionalShift p N).permMatrix ℂ*sourceCore p N 19*((sourceOptionalShift p N).permMatrix ℂ).conjTranspose)*
      (sourceOptionalFlip p N).permMatrix ℂ‖ ≤ _
  rw [source_optional_B]
  simp only [seriesMatrix,perm_conj_diagonal]
  apply permutationSeries_commutator _ _ _ (fun i => optionalDigit_bounds _ _) N
  intro i j hj hjN
  change optionalDigit (wordMask p N)
      (sourceOptionalRead p N (((sourceOptionalShift p N)^j) (sourceOptionalFlip p N i))) =
    optionalDigit (wordMask p N) (sourceOptionalRead p N (((sourceOptionalShift p N)^j) i))
  rw [permutation_map_power _ _ _ (sourceOptionalShift_read p N),
    permutation_map_power _ _ _ (sourceOptionalShift_read p N),sourceOptionalFlip_read]
  exact optionalFlip_preserves_prefix (incrementWord N) (wordMask p N) N
    (wordMask_capacity p N) j hj hjN (sourceOptionalRead p N i)

theorem source_optional_tail_op_defect (p : CounterProgram) (N : ℕ) :
    ‖Poly.eval (sourceTuple p N) (pc (sv p 22) (conjP (sv p 12) (sv p 19)))‖ ≤ (1/4:ℝ)^N := by
  simpa only [pc,conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_adj,
    sourceTuple_core p N 22 (by omega),sourceTuple_core p N 12 (by omega),
    sourceTuple_core p N 19 (by omega)] using source_optional_tail_norm p N

end
end E2.FiniteConstruction