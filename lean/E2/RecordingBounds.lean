import E2.RecordingWords

namespace E2.Recording
noncomputable section
open Companion.Analytic
open scoped BigOperators Matrix.Norms.L2Operator
set_option maxHeartbeats 300000

theorem familyNorm_eq_sqrt {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : familyNorm A=Real.sqrt (∑ i, hs (A i)^2) := by
  rw [←familyNorm_sq A,Real.sqrt_sq (familyNorm_nonneg _)]

theorem hs_stack_eq_sqrt {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
    (A : ι → Matrix α β ℂ) : hs (stack A)=Real.sqrt (∑ i, hs (A i)^2) := familyNorm_eq_sqrt A

theorem familyNorm_stack_eq_sqrt {ι κ α β : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    (A : ι → κ → Matrix α β ℂ) :
    familyNorm (fun i => stack (A i))=Real.sqrt (∑ i, ∑ k, hs (A i k)^2) := by
  rw [familyNorm_eq_sqrt]
  simp only [hsNorm_sq,hsSquared,stack,Fintype.sum_prod_type]

theorem column_branch_bound {ι α : Type*} [Fintype ι] [Fintype α] {d : ℕ}
    (K : ι → Mat d) (hK : ∑ a, K a*(K a).conjTranspose=1)
    (X : Mat d) (C : Matrix α (Fin d) ℂ) :
    familyNorm (fun a => C*K a*X)≤hs (C*X)+‖C‖*familyNorm (fun a => comm (K a) X) := by
  have he : (fun a => C*K a*X)=(fun a => (C*X)*K a+C*comm (K a) X) := by
    funext a
    simp only [comm,Companion.Analytic.comm,Matrix.mul_sub,Matrix.mul_assoc]
    abel
  rw [he]
  have hfirst : familyNorm (fun a => (C*X)*K a)=hs (C*X) := by
    apply (sq_eq_sq₀ (familyNorm_nonneg _) (hsNorm_nonneg _)).mp
    rw [familyNorm_sq,parseval_right K hK]
  exact (familyNorm_add _ _).trans (by
    rw [hfirst]
    exact add_le_add (le_refl _) (familyNorm_rectangular_mul C (fun a => comm (K a) X)))

theorem single_commutator_bound {d n : ℕ} (P : Fin n → Mat d) (X : Mat d)
    (η : ℝ) (hη : 0≤η) (hn : n≤3) (h : ∀ a, hs (comm (P a) X)≤η) :
    familyNorm (fun a => comm (P a) X)≤Real.sqrt 3*η := by
  have hsq : familyNorm (fun a => comm (P a) X)^2≤3*η^2 := by
    rw [familyNorm_sq]
    calc
      _≤∑ a : Fin n, η^2 := Finset.sum_le_sum (fun a _ => pow_le_pow_left₀ (hsNorm_nonneg _) (h a) 2)
      _=(n:ℝ)*η^2 := by simp
      _≤3*η^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (sq_nonneg η)
  have hsqrt : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply (sq_le_sq₀ (familyNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hη)).mp
  nlinarith

/-- Equation (8.2) for arbitrary finite alphabets of size at most three and an
arbitrary rectangular column. Completeness is used on both sides; commutators
between different PVMs and branch probabilities are not used. -/
theorem recorded_column_bound {α : Type*} [Fintype α] {d m : ℕ} {o : Fin m → ℕ}
    (P : ∀ i, Fin (o i) → Mat d) (hP : ∀ i, ∑ a, (P i a).conjTranspose*P i a=1)
    (hPc : ∀ i, ∑ a, P i a*(P i a).conjTranspose=1) (ho : ∀ i, o i≤3)
    (X : Mat d) (C : Matrix α (Fin d) ℂ) (η a L : ℝ) (hη : 0≤η) (hL : 0≤L)
    (hstate : ∀ i b, hs (comm (P i b) X)≤η) (hcolumn : ‖C‖≤L) (herror : hs (C*X)≤a) :
    familyNorm (fun b : Record o => C*word P b*X)≤a+L*m*Real.sqrt 3*η := by
  have hcomm := record_commutator P hP hPc X
  have hsum : (∑ i, familyNorm (fun b => comm (P i b) X))≤(m:ℝ)*(Real.sqrt 3*η) := by
    calc
      _≤∑ i : Fin m, Real.sqrt 3*η :=
        Finset.sum_le_sum (fun i _ => single_commutator_bound (P i) X η hη (ho i) (hstate i))
      _=_ := by simp
  have hbound := column_branch_bound (word P) (record_coComplete P hPc) X C
  calc
    _≤hs (C*X)+‖C‖*familyNorm (fun b : Record o => comm (word P b) X) := hbound
    _≤a+L*((m:ℝ)*(Real.sqrt 3*η)) := by
      exact add_le_add herror
        (mul_le_mul hcolumn (hcomm.trans hsum) (familyNorm_nonneg _) hL)
    _=_ := by ring

end
end E2.Recording
