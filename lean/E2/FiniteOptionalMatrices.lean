import E2.FiniteOptionalSlots

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

def optionalBackward {α : Type*} {k : ℕ} (s : Equiv.Perm α) (f : α → Bool) :
    Equiv.Perm (α × Bits k) :=
  (skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm

def optionalFlag {α : Type*} {k : ℕ} (f : α → Bool) (z : α × Bits k) : ℝ :=
  if f z.1 then 1 else 0

theorem optionalFlag_bounds {α : Type*} {k : ℕ} (f : α → Bool) (z : α × Bits k) :
    0 ≤ optionalFlag f z ∧ optionalFlag f z ≤ 1 := by
  cases h : f z.1 <;> norm_num [optionalFlag,h]

def seriesMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (s : Equiv.Perm α) (q : α → ℝ) : Matrix α α ℂ :=
  Matrix.diagonal (fun x => (permutationSeries s q x:ℂ))

theorem seriesMatrix_domain {α : Type*} [Fintype α] [DecidableEq α]
    (s : Equiv.Perm α) (q : α → ℝ) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    (seriesMatrix s q).PosSemidef ∧ (1-seriesMatrix s q).PosSemidef :=
  diagonal_positive_contraction _ (permutationSeries_bounds s q hq)

theorem seriesMatrix_affine {α : Type*} [Fintype α] [DecidableEq α]
    (s : Equiv.Perm α) (q : α → ℝ) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    s.permMatrix ℂ*seriesMatrix s q*(s.permMatrix ℂ).conjTranspose =
      (4:ℂ) • seriesMatrix s q-(3:ℂ) • Matrix.diagonal (fun x => (q x:ℂ)) := by
  rw [seriesMatrix,perm_conj_diagonal]
  ext i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,seriesMatrix]
    exact_mod_cast permutationSeries_affine s q hq i
  · simp [seriesMatrix,Matrix.diagonal_apply,h]

theorem optionalFlip_involution {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool) :
    (optionalFlip (k := k) f).symm = optionalFlip f := by
  apply Equiv.ext
  intro z
  rfl

theorem optionalFlip_reflection {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} [NeZero k] (f : α → Bool) :
    ((optionalFlip (k := k) f).permMatrix ℂ).conjTranspose=(optionalFlip (k := k) f).permMatrix ℂ ∧
      (optionalFlip (k := k) f).permMatrix ℂ*(optionalFlip (k := k) f).permMatrix ℂ=1 := by
  have hs : ((optionalFlip (k := k) f).permMatrix ℂ).conjTranspose=(optionalFlip (k := k) f).permMatrix ℂ := by
    rw [Matrix.conjTranspose_permMatrix]
    exact congrArg (fun r : Equiv.Perm (α × Bits k) => r.permMatrix ℂ) (optionalFlip_involution f)
  exact ⟨hs,by simpa only [hs] using (perm_unitary (optionalFlip (k := k) f)).1⟩

theorem optionalDigit_flip {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool) (z : α × Bits k) :
    optionalDigit f (optionalFlip f z) = optionalFlag f z-optionalDigit f z := by
  rcases z with ⟨a,b⟩
  cases h : f a <;> simp [optionalFlip,optionalDigit,optionalFlag,h,flip_bit_same]

theorem optionalFlag_flip {α : Type*} {k : ℕ} [NeZero k] (f : α → Bool) (z : α × Bits k) :
    optionalFlag f (optionalFlip f z)=optionalFlag f z := rfl

theorem optional_digit_flip_matrix {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} [NeZero k] (f : α → Bool) :
    (optionalFlip (k := k) f).permMatrix ℂ*
      Matrix.diagonal (fun z => (optionalDigit f z:ℂ))*(optionalFlip (k := k) f).permMatrix ℂ =
      Matrix.diagonal (fun z => (optionalFlag f z:ℂ))-
        Matrix.diagonal (fun z => (optionalDigit f z:ℂ)) := by
  have hc := perm_conj_diagonal (optionalFlip (k := k) f) (fun z => (optionalDigit f z:ℂ))
  rw [(optionalFlip_reflection (k := k) f).1] at hc
  rw [hc,Matrix.diagonal_sub]
  congr 1
  funext z
  exact_mod_cast optionalDigit_flip f z

theorem optional_flag_flip_matrix {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} [NeZero k] (f : α → Bool) :
    (optionalFlip (k := k) f).permMatrix ℂ*
      Matrix.diagonal (fun z => (optionalFlag f z:ℂ))*(optionalFlip (k := k) f).permMatrix ℂ =
      Matrix.diagonal (fun z => (optionalFlag f z:ℂ)) := by
  have hc := perm_conj_diagonal (optionalFlip (k := k) f) (fun z => (optionalFlag f z:ℂ))
  rw [(optionalFlip_reflection (k := k) f).1] at hc
  rw [hc]
  rfl

theorem optionalFlag_series_flip {α : Type*} {k : ℕ} [NeZero k]
    (s : Equiv.Perm α) (f : α → Bool) (z : α × Bits k) :
    permutationSeries (optionalBackward s f) (optionalFlag f) (optionalFlip f z) =
      permutationSeries (optionalBackward s f) (optionalFlag f) z := by
  rcases z with ⟨x,b⟩
  unfold permutationSeries boundedSeries
  apply tsum_congr
  intro j
  congr 1
  change optionalFlag f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j)
    (x,if f x then flipWord 0 b else b)) =
    optionalFlag f (((skewShift s (rotateWord k).symm (fun a => if f a then 1 else 0)).symm^j) (x,b))
  rw [skewShift_backward_power,skewShift_backward_power]
  rfl

theorem optional_series_commutator {α : Type*} [Fintype α] [DecidableEq α]
    {k : ℕ} [NeZero k] (s : Equiv.Perm α) (f : α → Bool) (N : ℕ)
    (hk : ∀ x j, j ≤ N → activeWindow s f j x < k) :
    ‖(optionalFlip (k := k) f).permMatrix ℂ*
        ((optionalBackward s f).permMatrix ℂ*seriesMatrix (optionalBackward s f) (optionalDigit f)*
          ((optionalBackward s f).permMatrix ℂ).conjTranspose)-
      ((optionalBackward s f).permMatrix ℂ*seriesMatrix (optionalBackward s f) (optionalDigit f)*
          ((optionalBackward s f).permMatrix ℂ).conjTranspose)*(optionalFlip (k := k) f).permMatrix ℂ‖ ≤
      (1/4:ℝ)^N := by
  simp only [seriesMatrix,perm_conj_diagonal]
  apply permutationSeries_commutator _ _ _ (optionalDigit_bounds f) N
  intro z j hj hjN
  exact optionalFlip_preserves_prefix s f N hk j hj hjN z

end
end E2.FiniteConstruction