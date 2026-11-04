import E2.FiniteSourceCommutation

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

theorem source_optional_supported (p : CounterProgram) (N : ℕ) :
    (1-sourceCore p N 18)*sourceCore p N 21=0 := by
  change (1-sourceDiagonal N (finiteSlots p N) (fun z => optionalFlag (wordMask p N) z.1))*
    sourceDiagonal N (finiteSlots p N) (fun z => optionalDigit (wordMask p N) z.1)=0
  rw [sourceDiagonal_one_sub,sourceDiagonal_mul]
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [sourceDiagonal,Matrix.diagonal_apply_eq,Matrix.zero_apply]
    cases h : wordMask p N (sourceBasisEquiv N (finiteSlots p N) a).1.1 <;>
      simp [optionalFlag,optionalDigit,h]
  · simp [sourceDiagonal,Matrix.diagonal_apply,hab]

theorem source_optional_flip_flag (p : CounterProgram) (N : ℕ) :
    sourceCore p N 22*sourceCore p N 18*sourceCore p N 22=sourceCore p N 18 := by
  have hx : (sourceCore p N 22).conjTranspose=sourceCore p N 22 := by
    exact (sourceCore_domain p N ⟨22,by omega⟩).1
  calc
    _ = sourceCore p N 22*sourceCore p N 18*(sourceCore p N 22).conjTranspose := by rw [hx]
    _ = _ := sourceConj_diagonal N (finiteSlots p N) (addressLift (optionalFlip (wordMask p N))) _

theorem source_optional_flip_digit (p : CounterProgram) (N : ℕ) :
    sourceCore p N 22*sourceCore p N 21*sourceCore p N 22=sourceCore p N 18-sourceCore p N 21 := by
  have hx : (sourceCore p N 22).conjTranspose=sourceCore p N 22 := by
    exact (sourceCore_domain p N ⟨22,by omega⟩).1
  calc
    _ = sourceCore p N 22*sourceCore p N 21*(sourceCore p N 22).conjTranspose := by rw [hx]
    _ = sourceDiagonal N (finiteSlots p N) (fun z => optionalDigit (wordMask p N) (optionalFlip (wordMask p N) z.1)) :=
      sourceConj_diagonal N (finiteSlots p N) (addressLift (optionalFlip (wordMask p N))) _
    _ = _ := by
      change _=sourceDiagonal N (finiteSlots p N) (fun z => optionalFlag (wordMask p N) z.1)-
        sourceDiagonal N (finiteSlots p N) (fun z => optionalDigit (wordMask p N) z.1)
      rw [sourceDiagonal_sub]
      congr 1
      funext z
      exact optionalDigit_flip _ _

theorem source_optional_flip_series (p : CounterProgram) (N : ℕ) :
    sourceCore p N 22*sourceCore p N 20=sourceCore p N 20*sourceCore p N 22 := by
  apply sourcePerm_diagonal_commute
  intro z
  exact optionalFlag_series_flip (incrementWord N) (wordMask p N) z.1

theorem source_optional_exact_polynomials (p : CounterProgram) (N : ℕ) :
    ∀ r∈[(1-sv p 18)*sv p 21,
      conjP (sv p 12) (sv p 19)-(4*sv p 19-3*sv p 21),
      conjP (sv p 12) (sv p 20)-(4*sv p 20-3*sv p 18),
      sv p 22*sv p 18*sv p 22-sv p 18,
      sv p 22*sv p 21*sv p 22-(sv p 18-sv p 21),pc (sv p 22) (sv p 20)],
      Poly.eval (sourceTuple p N) r=0 := by
  intro r hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [pc,conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_one,Poly.eval_adj,
      Poly.eval_four,Poly.eval_three,sourceTuple_core p N 12 (by omega),sourceTuple_core p N 18 (by omega),
      sourceTuple_core p N 19 (by omega),sourceTuple_core p N 20 (by omega),
      sourceTuple_core p N 21 (by omega),sourceTuple_core p N 22 (by omega),Matrix.smul_mul,Matrix.one_mul]
  · exact source_optional_supported p N
  · exact sub_eq_zero.mpr (source_optional_affine_B p N)
  · exact sub_eq_zero.mpr (source_optional_affine_C p N)
  · exact sub_eq_zero.mpr (source_optional_flip_flag p N)
  · exact sub_eq_zero.mpr (source_optional_flip_digit p N)
  · exact sub_eq_zero.mpr (source_optional_flip_series p N)

theorem source_carry_exact_commutations (p : CounterProgram) (N : ℕ) :
    Poly.eval (sourceTuple p N) (pc (sv p 1) (conjP (sv p 2) (sv p 14)))=0 ∧
      Poly.eval (sourceTuple p N) (pc (sv p 14) (sv p 0))=0 := by
  simp only [pc,conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_adj,
    sourceTuple_core p N 1 (by omega),sourceTuple_core p N 2 (by omega),
    sourceTuple_core p N 14 (by omega),sourceTuple_core p N 0 (by omega)]
  constructor
  · simp only [sourceCore]
    rw [sourceConj_diagonal]
    exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)
  · exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)

end
end E2.FiniteConstruction
