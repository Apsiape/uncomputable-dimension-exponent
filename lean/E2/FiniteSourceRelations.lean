import E2.FiniteSourceRelationLists

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

theorem sourceCertified_workspace (p : CounterProgram) (N : ℕ) :
    SourceCertified p N (commList (sv p 17::sourceWork p) (sv p 17::sourceWork p)) ∧
      SourceCertified p N (commList (sv p 17::sourceWork p)
        [sv p 0,sv p 4,sv p 8,sv p 15,sv p 16,sv p 18]) := by
  constructor
  · exact sourceCertified_commList p N _ _ (fun w hw v hv => source_work_commutations p N w v hw (Or.inl hv))
  · exact sourceCertified_commList p N _ _ (fun w hw v hv => source_work_commutations p N w v hw (Or.inr hv))

theorem sourceCertified_counter_zero (p : CounterProgram) (N : ℕ) :
    SourceCertified p N ((List.finRange p.counters).map (fun i =>
      sr p i-(sz p i+Poly.const (1/2)*(1-sz p i)*ss p i))) := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  exact source_zero_defect p N _ (source_zero_test_polynomial p N i)

theorem sourceCertified_control_orthogonal (p : CounterProgram) (N : ℕ) :
    SourceCertified p N ((List.finRange p.controls).flatMap (fun q =>
      ((List.finRange p.controls).filter (· != q)).map (fun q' => sq p q*sq p q'))) := by
  intro r hr
  obtain ⟨q,hq,q',hq',rfl⟩ := (by simpa only [List.mem_flatMap,List.mem_map] using hr :
    ∃ q∈List.finRange p.controls, ∃ q'∈((List.finRange p.controls).filter (· != q)), sq p q*sq p q'=r)
  have hne : q≠q' := by
    intro he
    have h := (List.mem_filter.mp hq').2
    subst q'
    simp at h
  exact source_zero_defect p N _ (source_control_orthogonal p N q q' hne)

theorem sourceCertified_counter_updates (p : CounterProgram) (N : ℕ) :
    SourceCertified p N ((List.finRange p.counters).flatMap (fun i =>
      [sv p 17*sr p i-sv p 17*initialCounter p i,
       conjP (sv p 13).adj (sr p i)-(conjP (sv p 13).adj (sv p 17)*initialCounter p i+
         (1-conjP (sv p 13).adj (sv p 17))*nextCounter p i)])) := by
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl | rfl
  · exact source_zero_defect p N _ (source_counter_initialization p N i)
  · exact source_zero_defect p N _ (source_counter_transition p N i)

theorem sourceCertified_control_updates (p : CounterProgram) (N : ℕ) :
    SourceCertified p N ((List.finRange p.controls).flatMap (fun i =>
      [sv p 17*sq p i-sv p 17*initialControl p i,
       conjP (sv p 13).adj (sq p i)-(conjP (sv p 13).adj (sv p 17)*initialControl p i+
         (1-conjP (sv p 13).adj (sv p 17))*nextControl p i)])) := by
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl | rfl
  · exact source_zero_defect p N _ (source_control_initialization p N i)
  · exact source_zero_defect p N _ (source_control_transition p N i)

theorem sourceCertified_optional (p : CounterProgram) (N : ℕ) :
    SourceCertified p N [(1-sv p 18)*sv p 21,
     pc (sv p 19) (sv p 21),pc (sv p 19) (sv p 18),pc (sv p 20) (sv p 21),pc (sv p 20) (sv p 18),
     pc (sv p 19) (sv p 20),
     conjP (sv p 12) (sv p 19)-(4*sv p 19-3*sv p 21),
     conjP (sv p 12) (sv p 20)-(4*sv p 20-3*sv p 18),
     sv p 22*sv p 18*sv p 22-sv p 18,
     sv p 22*sv p 21*sv p 22-(sv p 18-sv p 21),
     pc (sv p 22) (conjP (sv p 12) (sv p 19)),pc (sv p 22) (sv p 20)] := by
  intro r hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp
  · exact source_zero_defect p N _ (source_core_commutator p N 19 21 (by omega) (by omega)
      (sourceCore_diagonals_commute p N 19 21 (by simp [sourceDiagonalIndices]) (by simp [sourceDiagonalIndices])))
  · exact source_zero_defect p N _ (source_core_commutator p N 19 18 (by omega) (by omega)
      (sourceCore_diagonals_commute p N 19 18 (by simp [sourceDiagonalIndices]) (by simp [sourceDiagonalIndices])))
  · exact source_zero_defect p N _ (source_core_commutator p N 20 21 (by omega) (by omega)
      (sourceCore_diagonals_commute p N 20 21 (by simp [sourceDiagonalIndices]) (by simp [sourceDiagonalIndices])))
  · exact source_zero_defect p N _ (source_core_commutator p N 20 18 (by omega) (by omega)
      (sourceCore_diagonals_commute p N 20 18 (by simp [sourceDiagonalIndices]) (by simp [sourceDiagonalIndices])))
  · exact source_zero_defect p N _ (source_core_commutator p N 19 20 (by omega) (by omega)
      (sourceCore_diagonals_commute p N 19 20 (by simp [sourceDiagonalIndices]) (by simp [sourceDiagonalIndices])))
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp
  · exact (source_optional_tail_op_defect p N).trans (by
      have h : 0≤(1/4:ℝ)^N := by positivity
      linarith)
  · apply source_zero_defect
    apply source_optional_exact_polynomials p N
    simp

theorem sourceCertified_misc (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    let v := sv p
    let e00 := (1-v 1)*(1-conjP (v 2) (v 1))
    let e1 := v 1*(1-conjP (v 2) (v 1))
    SourceCertified p N [guardRelation (v 0) (v 1) (v 2) (v 3) (v 12),
     guardRelation (v 8) (v 9) (v 10) (v 11) (v 13),
     v 14-((1-v 1)+Poly.const (1/4)*v 1*conjP (v 2) (v 14)),
     pc (v 1) (conjP (v 2) (v 14)),pc (v 14) (v 0),
     conjP (v 12).adj (v 0)-(v 0-1+Poly.const (7/4)*v 14),
     v 15-(e1+e00*conjP (v 2^2) (v 15)),
     v 16-((1-e00)+Poly.const (1/2)*e00*conjP (v 2^2) (v 16)),
     v 17-((1-v 5)+v 5*(1-v 9)*conjP (v 6*v 10) (v 17))] := by
  dsimp only
  intro r hr
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (source_address_guard_op_defect p N (by omega)).trans (by
      have h : 0≤(1/4:ℝ)^N := by positivity
      linarith)
  · exact (source_time_guard_op_defect p N (by omega)).trans (by
      have h : 0≤(1/4:ℝ)^N := by positivity
      linarith)
  · exact source_zero_defect p N _ (source_carry_recursion_polynomial p N (by omega))
  · exact source_zero_defect p N _ (source_carry_exact_commutations p N).1
  · exact source_zero_defect p N _ (source_carry_exact_commutations p N).2
  · exact (source_carry_op_defect p N).trans (by
      have h : 0≤(1/4:ℝ)^N := by positivity
      linarith)
  · exact source_zero_defect p N _ (source_decoding_polynomials p N hN hEven).1
  · exact source_zero_defect p N _ (source_decoding_polynomials p N hN hEven).2
  · exact source_zero_defect p N _ (source_reset_recursion_polynomial p N (by omega))

theorem sourceCertified_singleton (p : CounterProgram) (N : ℕ) (r : SourcePoly p)
    (h : Poly.eval (sourceTuple p N) r=0) : SourceCertified p N [r] := by
  intro x hx
  have he : x=r := by simpa only [List.mem_cons,List.mem_nil_iff,or_false] using hx
  subst x
  exact source_zero_defect p N r h

theorem sourceTuple_all_relations (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    ∀ r∈(sourcePresentation p).relations,
      ‖Poly.eval (sourceTuple p N) r‖ ≤ 3*(1/4:ℝ)^N := by
  change SourceCertified p N (sourceRelations p)
  unfold sourceRelations
  simp only [Id.run,pure,sourceCertified_append,and_assoc]
  refine ⟨sourceCertified_clock p N (by omega) 0,sourceCertified_clock p N (by omega) 1,
    sourceCertified_clock p N (by omega) 2,?_,?_,?_,sourceCertified_misc p N hN hEven,
    sourceCertified_counter_zero p N,sourceCertified_control_orthogonal p N,
    sourceCertified_singleton p N _ (source_control_partition p N),sourceCertified_counter_updates p N,
    sourceCertified_control_updates p N,sourceCertified_singleton p N _ (source_halt_flag_polynomial p N),
    ?_,?_,(sourceCertified_workspace p N).1,(sourceCertified_workspace p N).2,
    sourceCertified_optional p N,?_⟩
  · apply sourceCertified_core_cross p N [0,1,2,3,12,14] [4,5,6,7]
    intro a ha b hb
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at *
    omega
  · apply sourceCertified_core_cross p N [0,1,2,3,12,14] [8,9,10,11,13]
    intro a ha b hb
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at *
    omega
  · apply sourceCertified_core_cross p N [4,5,6,7] [8,9,10,11,13]
    intro a ha b hb
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at *
    omega
  · apply sourceCertified_core_diagonal p N [15,16,18] [15,16,18]
    all_goals intro a ha; simp only [sourceDiagonalIndices,List.mem_cons,List.mem_nil_iff,or_false] at *; omega
  · apply sourceCertified_core_cross p N [15,16,18] [0,4,5,6,7,8,9,10,11,13]
    intro a ha b hb
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at *
    omega
  · apply sourceCertified_core_cross p N [19,20,21,22] [0,4,5,6,7,8,9,10,11,13]
    intro a ha b hb
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at *
    omega

end
end E2.FiniteConstruction
