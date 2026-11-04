import E2.FiniteListClocks

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem source_clock_affine_op_defect (p : CounterProgram) (N : ℕ) (i : Fin 3) :
    ‖Poly.eval (sourceTuple p N) (conjP (sv p (4*i.val+2)) (sv p (4*i.val))-
      (4*sv p (4*i.val)-3*sv p (4*i.val+1)))‖ ≤ 3*(1/4:ℝ)^N := by
  have hi := i.isLt
  have ha : 4*i.val<23 := by omega
  have hp : 4*i.val+1<23 := by omega
  have ht : 4*i.val+2<23 := by omega
  have he : Poly.eval (sourceTuple p N) (conjP (sv p (4*i.val+2)) (sv p (4*i.val))-
      (4*sv p (4*i.val)-3*sv p (4*i.val+1))) =
      sourceCore p N (4*i.val+2)*sourceCore p N (4*i.val)*(sourceCore p N (4*i.val+2)).conjTranspose-
        ((4:ℂ) • sourceCore p N (4*i.val)-(3:ℂ) • sourceCore p N (4*i.val+1)) := by
    simp only [conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_adj,Poly.eval_four,Poly.eval_three,
      sourceTuple_core p N (4*i.val) ha,sourceTuple_core p N (4*i.val+1) hp,
      sourceTuple_core p N (4*i.val+2) ht,Matrix.smul_mul,Matrix.one_mul]
  rw [he]
  fin_cases i
  · exact (source_clock_affine_norms p N).1
  · exact (source_clock_affine_norms p N).2.1
  · exact (source_clock_affine_norms p N).2.2

theorem source_clock_tail_op_defect (p : CounterProgram) (N : ℕ) (hN : 0<N) (i : Fin 3) :
    ‖Poly.eval (sourceTuple p N)
      (pc (sv p (4*i.val+3)) (conjP (sv p (4*i.val+2)) (sv p (4*i.val))))‖ ≤ 3*(1/4:ℝ)^N := by
  have hi := i.isLt
  have ha : 4*i.val<23 := by omega
  have ht : 4*i.val+2<23 := by omega
  have hx : 4*i.val+3<23 := by omega
  have he : Poly.eval (sourceTuple p N)
      (pc (sv p (4*i.val+3)) (conjP (sv p (4*i.val+2)) (sv p (4*i.val)))) =
      sourceCore p N (4*i.val+3)*
        (sourceCore p N (4*i.val+2)*sourceCore p N (4*i.val)*(sourceCore p N (4*i.val+2)).conjTranspose)-
      (sourceCore p N (4*i.val+2)*sourceCore p N (4*i.val)*(sourceCore p N (4*i.val+2)).conjTranspose)*
        sourceCore p N (4*i.val+3) := by
    simp only [pc,conjP,Poly.eval_sub,Poly.eval_mul,Poly.eval_adj,
      sourceTuple_core p N (4*i.val) ha,sourceTuple_core p N (4*i.val+2) ht,
      sourceTuple_core p N (4*i.val+3) hx]
  rw [he]
  fin_cases i
  · exact (source_clock_tail_norms p N hN).1
  · exact (source_clock_tail_norms p N hN).2.1
  · exact (source_clock_tail_norms p N hN).2.2

end
end E2.FiniteConstruction