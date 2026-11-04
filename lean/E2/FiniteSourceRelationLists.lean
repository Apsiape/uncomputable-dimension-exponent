import E2.FiniteSourceExactClocks
import E2.FiniteSourceConditions
import E2.FiniteSourceUpdates
import E2.FiniteSourceAddressGuard
import E2.FiniteSourceTimeGuard

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false

def SourceCertified (p : CounterProgram) (N : ℕ) (rs : List (SourcePoly p)) : Prop :=
  ∀ r∈rs, ‖Poly.eval (sourceTuple p N) r‖ ≤ 3*(1/4:ℝ)^N

theorem sourceCertified_append (p : CounterProgram) (N : ℕ) (xs ys : List (SourcePoly p)) :
    SourceCertified p N (xs++ys) ↔ SourceCertified p N xs ∧ SourceCertified p N ys := by
  simp only [SourceCertified,List.mem_append,or_imp,forall_and]

theorem sourceCertified_cons (p : CounterProgram) (N : ℕ) (r : SourcePoly p) (rs : List (SourcePoly p)) :
    SourceCertified p N (r::rs) ↔
      ‖Poly.eval (sourceTuple p N) r‖ ≤ 3*(1/4:ℝ)^N ∧ SourceCertified p N rs := by
  simp only [SourceCertified,List.mem_cons,forall_eq_or_imp]

theorem sourceCertified_nil (p : CounterProgram) (N : ℕ) : SourceCertified p N [] := by
  simp [SourceCertified]

theorem source_zero_defect (p : CounterProgram) (N : ℕ) (r : SourcePoly p)
    (h : Poly.eval (sourceTuple p N) r=0) : ‖Poly.eval (sourceTuple p N) r‖ ≤ 3*(1/4:ℝ)^N := by
  rw [h,norm_zero]
  positivity

theorem sourceCertified_clock (p : CounterProgram) (N : ℕ) (hN : 0<N) (i : Fin 3) :
    SourceCertified p N (clockRelations (sv p (4*i.val)) (sv p (4*i.val+1))
      (sv p (4*i.val+2)) (sv p (4*i.val+3))) := by
  unfold clockRelations
  simp only [sourceCertified_cons,sourceCertified_nil,and_true]
  exact ⟨source_zero_defect p N _ (source_clock_exact p N hN i).1,
    source_clock_affine_op_defect p N i,
    source_zero_defect p N _ (source_clock_exact p N hN i).2,
    source_clock_tail_op_defect p N hN i⟩

theorem sourceCertified_commList (p : CounterProgram) (N : ℕ) (xs ys : List (SourcePoly p))
    (h : ∀ x∈xs, ∀ y∈ys, Poly.eval (sourceTuple p N) (pc x y)=0) :
    SourceCertified p N (commList xs ys) := by
  intro r hr
  obtain ⟨x,hx,y,hy,rfl⟩ := (by simpa only [commList,List.mem_flatMap,List.mem_map] using hr :
    ∃ x∈xs, ∃ y∈ys, pc x y=r)
  exact source_zero_defect p N _ (h x hx y hy)

theorem source_core_commutator (p : CounterProgram) (N a b : ℕ) (ha : a<23) (hb : b<23)
    (h : sourceCore p N a*sourceCore p N b=sourceCore p N b*sourceCore p N a) :
    Poly.eval (sourceTuple p N) (pc (sv p a) (sv p b))=0 := by
  simpa only [pc,Poly.eval_sub,Poly.eval_mul,sourceTuple_core p N a ha,
    sourceTuple_core p N b hb] using sub_eq_zero.mpr h

theorem sourceCertified_core_cross (p : CounterProgram) (N : ℕ) (as bs : List ℕ)
    (h : ∀ a∈as, ∀ b∈bs, a<23 ∧ b<23 ∧
      ((a∈[0,1,2,3,12,14] ∧ b∈[4,5,6,7,8,9,10,11,13]) ∨
       (a∈[4,5,6,7] ∧ b∈[8,9,10,11,13]) ∨
       (a∈[15,16,18,19,20,21,22] ∧ b∈[0,4,5,6,7,8,9,10,11,13]))) :
    SourceCertified p N (commList (as.map (sv p)) (bs.map (sv p))) := by
  apply sourceCertified_commList
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
  obtain ⟨ha',hb',hc⟩ := h a ha b hb
  exact source_core_commutator p N a b ha' hb' (source_core_cross_commutations p N a b hc)

theorem sourceCertified_core_diagonal (p : CounterProgram) (N : ℕ) (as bs : List ℕ)
    (ha : ∀ a∈as, a∈sourceDiagonalIndices) (hb : ∀ b∈bs, b∈sourceDiagonalIndices) :
    SourceCertified p N (commList (as.map (sv p)) (bs.map (sv p))) := by
  apply sourceCertified_commList
  intro x hx y hy
  obtain ⟨a,ha',rfl⟩ := List.mem_map.mp hx
  obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hy
  have ha'' := ha a ha'
  have hb'' := hb b hb'
  have hlt (n : ℕ) (hn : n∈sourceDiagonalIndices) : n<23 := by
    simp only [sourceDiagonalIndices,List.mem_cons,List.mem_nil_iff,or_false] at hn
    omega
  exact source_core_commutator p N a b (hlt a ha'') (hlt b hb'')
    (sourceCore_diagonals_commute p N a b ha'' hb'')

end
end E2.FiniteConstruction
