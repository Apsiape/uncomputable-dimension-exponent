import E2.FiniteSourceCommutation
import E2.FiniteSourceClockPolynomials
import E2.FiniteSourceDecoding
import E2.FiniteSourceResetCarry

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

theorem flipFirstWord_head (N : ℕ) (hN : 0<N) (b : BinaryWord N) :
    boolValue ((flipFirstWord N b).val.headD false)=1-boolValue (b.val.headD false) := by
  change boolValue ((listFlipFirst b.val).headD false)=1-boolValue (b.val.headD false)
  have hl := b.property
  cases hb : b.val with
  | nil => simp only [hb,List.length_nil] at hl; omega
  | cons x xs => cases x <;> norm_num [flipFirstWord,listFlipFirst,hb,boolValue]

theorem source_flip_digit (N k : ℕ) (hN : 0<N) (s : Equiv.Perm (SourceBasis N k))
    (w : SourceBasis N k → BinaryWord N) (hs : Function.Involutive s)
    (hw : ∀ z, w (s z)=flipFirstWord N (w z)) :
    (sourcePerm N k s).permMatrix ℂ*sourceDiagonal N k (fun z => boolValue ((w z).val.headD false))*
        (sourcePerm N k s).permMatrix ℂ =
      1-sourceDiagonal N k (fun z => boolValue ((w z).val.headD false)) := by
  have hx := source_reflection N k s hs
  calc
    _ = (sourcePerm N k s).permMatrix ℂ*sourceDiagonal N k (fun z => boolValue ((w z).val.headD false))*
        ((sourcePerm N k s).permMatrix ℂ).conjTranspose := by rw [hx.1]
    _ = _ := by
      rw [sourceConj_diagonal,sourceDiagonal_one_sub]
      congr 1
      funext z
      rw [hw,flipFirstWord_head N hN]

theorem source_clock_exact (p : CounterProgram) (N : ℕ) (hN : 0<N) (i : Fin 3) :
    Poly.eval (sourceTuple p N) (pc (sv p (4*i.val)) (sv p (4*i.val+1)))=0 ∧
      Poly.eval (sourceTuple p N)
        (sv p (4*i.val+3)*sv p (4*i.val+1)*sv p (4*i.val+3)-(1-sv p (4*i.val+1)))=0 := by
  have hi := i.isLt
  have he (n : ℕ) (hn : n<23) := sourceTuple_core p N n hn
  simp only [pc,Poly.eval_sub,Poly.eval_mul,Poly.eval_one,
    he (4*i.val) (by omega),he (4*i.val+1) (by omega),he (4*i.val+3) (by omega)]
  fin_cases i
  all_goals constructor
  all_goals simp only [sourceCore]
  · exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)
  · apply sub_eq_zero.mpr
    exact source_flip_digit N (finiteSlots p N) hN
      (addressLift (addressFlip p N (finiteSlots p N))) (fun z => z.1.1)
      (prod_involutive _ _ (addressFlip_involutive p N _) (fun _ => rfl)) (fun _ => rfl)
  · exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)
  · apply sub_eq_zero.mpr
    exact source_flip_digit N (finiteSlots p N) hN
      (fuelLift (flipFirstWord N)) (fun z => z.2.1)
      (prod_involutive _ _ (fun _ => rfl)
        (prod_involutive _ _ (flipFirstWord_involutive N) (fun _ => rfl))) (fun _ => rfl)
  · exact sub_eq_zero.mpr (sourceDiagonal_commute _ _ _ _)
  · apply sub_eq_zero.mpr
    exact source_flip_digit N (finiteSlots p N) hN
      (timeLift (flipFirstWord N)) (fun z => z.2.2)
      (prod_involutive _ _ (fun _ => rfl)
        (prod_involutive _ _ (fun _ => rfl) (flipFirstWord_involutive N))) (fun _ => rfl)

theorem source_carry_recursion_polynomial (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    Poly.eval (sourceTuple p N)
      (sv p 14-((1-sv p 1)+Poly.const (1/4)*sv p 1*conjP (sv p 2) (sv p 14)))=0 := by
  simp only [conjP,Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_const,Poly.eval_one,
    Poly.eval_adj,sourceTuple_core p N 14 (by omega),sourceTuple_core p N 1 (by omega),
    sourceTuple_core p N 2 (by omega),Matrix.smul_mul,Matrix.one_mul]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  exact sub_eq_zero.mpr (source_carry_recursion_matrix p N hN)

theorem source_reset_recursion_polynomial (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    Poly.eval (sourceTuple p N)
      (sv p 17-((1-sv p 5)+sv p 5*(1-sv p 9)*conjP (sv p 6*sv p 10) (sv p 17)))=0 := by
  simp only [conjP,Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_one,Poly.eval_adj,
    sourceTuple_core p N 17 (by omega),sourceTuple_core p N 5 (by omega),sourceTuple_core p N 9 (by omega),
    sourceTuple_core p N 6 (by omega),sourceTuple_core p N 10 (by omega),Matrix.conjTranspose_mul]
  apply sub_eq_zero.mpr
  simpa only [Matrix.mul_assoc] using source_reset_recursion_matrix p N hN

theorem source_decoding_polynomials (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    let e00 := (1-sv p 1)*(1-conjP (sv p 2) (sv p 1))
    let e1 := sv p 1*(1-conjP (sv p 2) (sv p 1))
    Poly.eval (sourceTuple p N) (sv p 15-(e1+e00*conjP (sv p 2^2) (sv p 15)))=0 ∧
      Poly.eval (sourceTuple p N) (sv p 16-((1-e00)+Poly.const (1/2)*e00*conjP (sv p 2^2) (sv p 16)))=0 := by
  have hp : Poly.eval (sourceTuple p N) (sv p 2^2)=sourceCore p N 2*sourceCore p N 2 := by
    change Poly.eval _ (sv p 2*(sv p 2*1))=_
    simp only [Poly.eval_mul,Poly.eval_one,sourceTuple_core p N 2 (by omega),Matrix.mul_one]
  dsimp only
  simp only [conjP,Poly.eval_sub,Poly.eval_add,Poly.eval_mul,Poly.eval_one,Poly.eval_adj,Poly.eval_const,hp,
    sourceTuple_core p N 1 (by omega),sourceTuple_core p N 2 (by omega),
    sourceTuple_core p N 15 (by omega),sourceTuple_core p N 16 (by omega),
    Matrix.conjTranspose_mul,Matrix.smul_mul,Matrix.one_mul]
  constructor
  · apply sub_eq_zero.mpr
    simpa only [Matrix.mul_assoc] using source_decoding_L_matrix p N hN hEven
  · apply sub_eq_zero.mpr
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    simpa only [Matrix.mul_assoc] using source_decoding_R_matrix p N hN hEven

end
end E2.FiniteConstruction
