import E2.FiniteSourceDiagonal
import E2.FiniteSourceWorkspace
import E2.FiniteSourceOptional

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

theorem sourcePerm_diagonal_commute (N k : ℕ) (s : Equiv.Perm (SourceBasis N k))
    (v : SourceBasis N k → ℝ) (h : ∀ z, v (s z)=v z) :
    (sourcePerm N k s).permMatrix ℂ*sourceDiagonal N k v=
      sourceDiagonal N k v*(sourcePerm N k s).permMatrix ℂ := by
  have hc := sourceConj_diagonal N k s v
  have he : (fun z => v (s z))=v := funext h
  rw [he] at hc
  have ht := congrArg (fun a => a*(sourcePerm N k s).permMatrix ℂ) hc
  simpa only [Matrix.mul_assoc,(perm_unitary (sourcePerm N k s)).1,Matrix.mul_one] using ht

theorem sourceDiagonal_perm_commute (N k : ℕ) (v : SourceBasis N k → ℝ)
    (s : Equiv.Perm (SourceBasis N k)) (h : ∀ z, v (s z)=v z) :
    sourceDiagonal N k v*(sourcePerm N k s).permMatrix ℂ=
      (sourcePerm N k s).permMatrix ℂ*sourceDiagonal N k v :=
  (sourcePerm_diagonal_commute N k s v h).symm

theorem sourcePerm_perm_commute (N k : ℕ) (s t : Equiv.Perm (SourceBasis N k))
    (h : ∀ z, s (t z)=t (s z)) :
    (sourcePerm N k s).permMatrix ℂ*(sourcePerm N k t).permMatrix ℂ=
      (sourcePerm N k t).permMatrix ℂ*(sourcePerm N k s).permMatrix ℂ := by
  rw [←Matrix.permMatrix_mul,←Matrix.permMatrix_mul]
  congr 1
  apply Equiv.ext
  intro i
  apply (sourceBasisEquiv N k).injective
  simp only [Equiv.Perm.mul_apply,sourcePerm_basis]
  exact (h _).symm

macro "source_commute" : tactic => `(tactic|
  first
  | with_reducible exact sourceDiagonal_commute _ _ _ _
  | with_reducible exact sourcePerm_diagonal_commute _ _ _ _ (fun _ => rfl)
  | with_reducible exact sourceDiagonal_perm_commute _ _ _ _ (fun _ => rfl)
  | with_reducible exact sourcePerm_perm_commute _ _ _ _ (fun _ => rfl))

theorem source_core_cross_commutations (p : CounterProgram) (N : ℕ) (a b : ℕ)
    (h : (a∈[0,1,2,3,12,14] ∧ b∈[4,5,6,7,8,9,10,11,13]) ∨
      (a∈[4,5,6,7] ∧ b∈[8,9,10,11,13]) ∨
      (a∈[15,16,18,19,20,21,22] ∧ b∈[0,4,5,6,7,8,9,10,11,13])) :
    sourceCore p N a*sourceCore p N b=sourceCore p N b*sourceCore p N a := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sourceCore] <;> source_commute
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      simp only [sourceCore] <;> source_commute
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sourceCore] <;> source_commute

def sourceDiagonalIndices : List ℕ := [0,1,4,5,8,9,14,15,16,17,18,19,20,21]

theorem sourceCore_diagonal (p : CounterProgram) (N a : ℕ) (h : a∈sourceDiagonalIndices) :
    ∃ v, sourceCore p N a=sourceDiagonal N (finiteSlots p N) v := by
  simp only [sourceDiagonalIndices,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [sourceCore]; exact ⟨_,rfl⟩

theorem sourceCore_diagonals_commute (p : CounterProgram) (N a b : ℕ)
    (ha : a∈sourceDiagonalIndices) (hb : b∈sourceDiagonalIndices) :
    sourceCore p N a*sourceCore p N b=sourceCore p N b*sourceCore p N a := by
  obtain ⟨v,hv⟩ := sourceCore_diagonal p N a ha
  obtain ⟨w,hw⟩ := sourceCore_diagonal p N b hb
  rw [hv,hw]
  exact sourceDiagonal_commute _ _ _ _

def sourceWork (p : CounterProgram) : List (SourcePoly p) :=
  (List.finRange p.counters).flatMap (fun i => [sr p i,sz p i,ss p i]) ++
    (List.finRange p.controls).map (sq p)

theorem source_work_diagonal (p : CounterProgram) (N : ℕ) (w : SourcePoly p)
    (hw : w∈sv p 17::sourceWork p) :
    ∃ v, Poly.eval (sourceTuple p N) w=sourceDiagonal N (finiteSlots p N) v := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,sourceWork,List.mem_append,List.mem_flatMap,List.mem_map] at hw
  rcases hw with rfl | ⟨i,hi,hw⟩ | ⟨q,hq,rfl⟩
  · obtain ⟨v,hv⟩ := sourceCore_diagonal p N 17 (by simp [sourceDiagonalIndices])
    exact ⟨v,(sourceTuple_core p N 17 (by omega)).trans hv⟩
  · rcases hw with rfl | rfl | rfl
    · exact ⟨_,sourceTuple_sr p N i⟩
    · exact ⟨_,sourceTuple_sz p N i⟩
    · exact ⟨_,sourceTuple_ss p N i⟩
  · exact ⟨_,sourceTuple_sq p N q⟩

theorem source_work_commutations (p : CounterProgram) (N : ℕ) (w v : SourcePoly p)
    (hw : w∈sv p 17::sourceWork p)
    (hv : v∈sv p 17::sourceWork p ∨ v∈[sv p 0,sv p 4,sv p 8,sv p 15,sv p 16,sv p 18]) :
    Poly.eval (sourceTuple p N) (pc w v)=0 := by
  obtain ⟨a,ha⟩ := source_work_diagonal p N w hw
  have hb : ∃ b, Poly.eval (sourceTuple p N) v=sourceDiagonal N (finiteSlots p N) b := by
    rcases hv with hv | hv
    · exact source_work_diagonal p N v hv
    · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 0 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 0 (by omega)).trans hb⟩
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 4 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 4 (by omega)).trans hb⟩
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 8 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 8 (by omega)).trans hb⟩
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 15 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 15 (by omega)).trans hb⟩
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 16 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 16 (by omega)).trans hb⟩
      · obtain ⟨b,hb⟩ := sourceCore_diagonal p N 18 (by simp [sourceDiagonalIndices])
        exact ⟨b,(sourceTuple_core p N 18 (by omega)).trans hb⟩

  obtain ⟨b,hb⟩ := hb
  simp only [pc,Poly.eval_sub,Poly.eval_mul,ha,hb]
  exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)

end
end E2.FiniteConstruction
