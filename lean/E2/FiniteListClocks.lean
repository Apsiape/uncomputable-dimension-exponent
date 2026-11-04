import E2.FiniteSourceCoordinates

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem listCoordinate_append (bs cs : List Bool) :
    listCoordinate (bs++cs)=listCoordinate bs+(1/4:ℝ)^bs.length*listCoordinate cs := by
  induction bs with
  | nil => simp [listCoordinate]
  | cons b bs ih =>
    simp only [List.cons_append,listCoordinate,List.length_cons,pow_succ,ih]
    ring

theorem listClock_affine (bs : List Bool) :
    listCoordinate (listRotate bs)-4*listCoordinate bs+3*boolValue (bs.headD false) =
      3*(1/4:ℝ)^bs.length*boolValue (bs.headD false) := by
  cases bs with
  | nil => norm_num [listRotate,listCoordinate,boolValue]
  | cons b bs =>
    simp only [listRotate,listCoordinate_append,listCoordinate,List.headD_cons,List.length_cons,pow_succ]
    ring

theorem boolValue_not (b : Bool) : boolValue (!b)=1-boolValue b := by cases b <;> norm_num [boolValue]

theorem listClock_tail_flip (b : Bool) (bs : List Bool) :
    listCoordinate (listRotate (listFlipFirst (b::bs)))-listCoordinate (listRotate (b::bs)) =
      3*(1/4:ℝ)^(bs.length+1)*(1-2*boolValue b) := by
  simp only [listFlipFirst,listRotate,listCoordinate_append,listCoordinate,boolValue_not,pow_succ]
  ring

def wordCoordinateMatrix {α : Type*} [DecidableEq α] {N : ℕ} (w : α → BinaryWord N) : Matrix α α ℂ :=
  Matrix.diagonal (fun i => (listCoordinate (w i).val:ℂ))

def wordDigitMatrix {α : Type*} [DecidableEq α] {N : ℕ} (w : α → BinaryWord N) : Matrix α α ℂ :=
  Matrix.diagonal (fun i => (boolValue ((w i).val.headD false):ℂ))

theorem wordDigitMatrix_norm {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (w : α → BinaryWord N) : ‖wordDigitMatrix w‖ ≤ 1 := by
  rw [wordDigitMatrix,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  cases h : (w i).val.headD false <;> norm_num [boolValue,h]

theorem wordClock_affine {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (w : α → BinaryWord N) (t : Equiv.Perm α)
    (ht : ∀ i, w (t i)=rotateBinary N (w i)) :
    t.permMatrix ℂ*wordCoordinateMatrix w*(t.permMatrix ℂ).conjTranspose-
      ((4:ℂ) • wordCoordinateMatrix w-(3:ℂ) • wordDigitMatrix w) =
      ((3*(1/4:ℝ)^N:ℝ):ℂ) • wordDigitMatrix w := by
  rw [wordCoordinateMatrix,perm_conj_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [wordCoordinateMatrix,wordDigitMatrix,Matrix.sub_apply,Matrix.smul_apply,
      Matrix.diagonal_apply_eq,smul_eq_mul]
    rw [ht]
    have h := listClock_affine (w i).val
    rw [(w i).property] at h
    have he : listCoordinate (listRotate (w i).val)-
        (4*listCoordinate (w i).val-3*boolValue ((w i).val.headD false)) =
        3*(1/4:ℝ)^N*boolValue ((w i).val.headD false) := by linarith
    exact_mod_cast he
  · simp [wordCoordinateMatrix,wordDigitMatrix,Matrix.diagonal_apply,hij]

theorem wordClock_affine_norm {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (w : α → BinaryWord N) (t : Equiv.Perm α)
    (ht : ∀ i, w (t i)=rotateBinary N (w i)) :
    ‖t.permMatrix ℂ*wordCoordinateMatrix w*(t.permMatrix ℂ).conjTranspose-
      ((4:ℂ) • wordCoordinateMatrix w-(3:ℂ) • wordDigitMatrix w)‖ ≤ 3*(1/4:ℝ)^N := by
  rw [wordClock_affine w t ht,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ)≤3*(1/4:ℝ)^N)]
  have h := wordDigitMatrix_norm w
  nlinarith [show (0:ℝ)≤3*(1/4:ℝ)^N by positivity]

theorem wordClock_tail_norm {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (hN : 0<N) (w : α → BinaryWord N) (t x : Equiv.Perm α)
    (ht : ∀ i, w (t i)=rotateBinary N (w i))
    (hx : ∀ i, w (x i)=flipFirstWord N (w i)) :
    ‖x.permMatrix ℂ*(t.permMatrix ℂ*wordCoordinateMatrix w*(t.permMatrix ℂ).conjTranspose)-
      (t.permMatrix ℂ*wordCoordinateMatrix w*(t.permMatrix ℂ).conjTranspose)*x.permMatrix ℂ‖ ≤
      3*(1/4:ℝ)^N := by
  rw [wordCoordinateMatrix,perm_conj_diagonal]
  apply perm_comm_diagonal_norm _ _ _ (by positivity)
  intro i
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [ht (x i),ht i,hx]
  change |listCoordinate (listRotate (listFlipFirst (w i).val))-
    listCoordinate (listRotate (w i).val)| ≤ _
  have hlen := (w i).property
  cases hb : (w i).val with
  | nil => simp only [hb,List.length_nil] at hlen; omega
  | cons b bs =>
    rw [listClock_tail_flip]
    simp only [hb,List.length_cons] at hlen
    rw [hlen,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤3*(1/4:ℝ)^N)]
    cases b <;> norm_num [boolValue]

/-- All three affine clock defects on the common source tuple. -/
theorem source_clock_affine_norms (p : CounterProgram) (N : ℕ) :
    (‖sourceCore p N 2*sourceCore p N 0*(sourceCore p N 2).conjTranspose-
        ((4:ℂ) • sourceCore p N 0-(3:ℂ) • sourceCore p N 1)‖ ≤ 3*(1/4:ℝ)^N) ∧
    (‖sourceCore p N 6*sourceCore p N 4*(sourceCore p N 6).conjTranspose-
        ((4:ℂ) • sourceCore p N 4-(3:ℂ) • sourceCore p N 5)‖ ≤ 3*(1/4:ℝ)^N) ∧
    (‖sourceCore p N 10*sourceCore p N 8*(sourceCore p N 10).conjTranspose-
        ((4:ℂ) • sourceCore p N 8-(3:ℂ) • sourceCore p N 9)‖ ≤ 3*(1/4:ℝ)^N) := by
  refine ⟨?_,?_,?_⟩
  · apply wordClock_affine_norm (fun i => (sourceBasisEquiv N (finiteSlots p N) i).1.1)
    intro i
    rw [sourcePerm_basis]
    rfl
  · apply wordClock_affine_norm (fun i => (sourceBasisEquiv N (finiteSlots p N) i).2.1)
    intro i
    rw [sourcePerm_basis]
    rfl
  · apply wordClock_affine_norm (fun i => (sourceBasisEquiv N (finiteSlots p N) i).2.2)
    intro i
    rw [sourcePerm_basis]
    rfl

theorem source_clock_tail_norms (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    (‖sourceCore p N 3*(sourceCore p N 2*sourceCore p N 0*(sourceCore p N 2).conjTranspose)-
      (sourceCore p N 2*sourceCore p N 0*(sourceCore p N 2).conjTranspose)*sourceCore p N 3‖ ≤ 3*(1/4:ℝ)^N) ∧
    (‖sourceCore p N 7*(sourceCore p N 6*sourceCore p N 4*(sourceCore p N 6).conjTranspose)-
      (sourceCore p N 6*sourceCore p N 4*(sourceCore p N 6).conjTranspose)*sourceCore p N 7‖ ≤ 3*(1/4:ℝ)^N) ∧
    (‖sourceCore p N 11*(sourceCore p N 10*sourceCore p N 8*(sourceCore p N 10).conjTranspose)-
      (sourceCore p N 10*sourceCore p N 8*(sourceCore p N 10).conjTranspose)*sourceCore p N 11‖ ≤ 3*(1/4:ℝ)^N) := by
  refine ⟨?_,?_,?_⟩
  · apply wordClock_tail_norm hN (fun i => (sourceBasisEquiv N (finiteSlots p N) i).1.1)
    · intro i; rw [sourcePerm_basis]; rfl
    · intro i; rw [sourcePerm_basis]; rfl
  · apply wordClock_tail_norm hN (fun i => (sourceBasisEquiv N (finiteSlots p N) i).2.1)
    · intro i; rw [sourcePerm_basis]; rfl
    · intro i; rw [sourcePerm_basis]; rfl
  · apply wordClock_tail_norm hN (fun i => (sourceBasisEquiv N (finiteSlots p N) i).2.2)
    · intro i; rw [sourcePerm_basis]; rfl
    · intro i; rw [sourcePerm_basis]; rfl
end
end E2.FiniteConstruction