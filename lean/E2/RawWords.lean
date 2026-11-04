import E2.Weighted

namespace E2
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Companion.Analytic

theorem weighted_add {d : ℕ} (s : State d) (a b : Mat d) :
    weighted s (a+b) ≤ weighted s a + weighted s b := by
  simpa only [weighted, Matrix.add_mul] using hsNorm_add_le (a*s.xi) (b*s.xi)

theorem comm_mul_left {d : ℕ} (a b z : Mat d) :
    comm (a*b) z = a*comm b z + comm a z*b := by
  simp only [comm, Companion.Analytic.comm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem comm_mul_right {d : ℕ} (a b z : Mat d) :
    comm a (b*z) = comm a b*z + b*comm a z := by
  simp only [comm, Companion.Analytic.comm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem norm_comm_contractions {d : ℕ} (a b : Mat d) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖comm a b‖ ≤ 2 := by
  change ‖a*b-b*a‖ ≤ 2
  calc
    _ ≤ ‖a*b‖+‖b*a‖ := norm_sub_le _ _
    _ ≤ ‖a‖*‖b‖+‖b‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 2 := by nlinarith [norm_nonneg a,norm_nonneg b]

theorem word_norm {d : ℕ} (hd : 0 < d) (xs : List (Mat d))
    (h : ∀ a ∈ xs, ‖a‖ ≤ 1) : ‖xs.prod‖ ≤ 1 := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.prod_cons]
    calc
      _ ≤ ‖a‖*‖xs.prod‖ := norm_mul_le _ _
      _ ≤ 1*1 := mul_le_mul (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))
        (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

theorem word_state_commutator {d : ℕ} (s : State d) (hd : 0 < d) (δ : ℝ) (hδ : 0 ≤ δ)
    (xs : List (Mat d)) (hn : ∀ a ∈ xs, ‖a‖ ≤ 1)
    (hc : ∀ a ∈ xs, hs (comm a s.xi) ≤ δ) :
    hs (comm xs.prod s.xi) ≤ xs.length*δ := by
  induction xs with
  | nil => simp [comm, Companion.Analytic.comm, hs, hsNorm, hsSquared]
  | cons a xs ih =>
    have hn' : ∀ b ∈ xs, ‖b‖ ≤ 1 := fun b hb => hn b (by simp [hb])
    have hc' : ∀ b ∈ xs, hs (comm b s.xi) ≤ δ := fun b hb => hc b (by simp [hb])
    rw [List.prod_cons, comm_mul_left]
    calc
      _ ≤ hs (a*comm xs.prod s.xi) + hs (comm a s.xi*xs.prod) := hsNorm_add_le _ _
      _ ≤ ‖a‖*hs (comm xs.prod s.xi)+hs (comm a s.xi)*‖xs.prod‖ :=
        add_le_add (operator_mul_hs _ _) (hs_mul_operator _ _)
      _ ≤ 1*(xs.length*δ)+δ*1 := by
        gcongr <;> first
        | exact hsNorm_nonneg _
        | exact hn a (by simp)
        | exact ih hn' hc'
        | exact hc a (by simp)
        | exact word_norm hd xs hn'
      _ = (a::xs).length*δ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- A fixed contraction against a raw conjugated word. The quadratic bound
accounts for every right-multiplication state cost, without spectral calculus. -/
theorem word_single_commutator {d : ℕ} (s : State d) (hd : 0 < d) (δ : ℝ) (hδ : 0 ≤ δ)
    (xs : List (Mat d)) (Y : Mat d) (hY : ‖Y‖ ≤ 1)
    (hn : ∀ a ∈ xs, ‖a‖ ≤ 1) (hc : ∀ a ∈ xs, hs (comm a s.xi) ≤ δ)
    (hbase : ∀ a ∈ xs, weighted s (comm a Y) ≤ δ) :
    weighted s (comm xs.prod Y) ≤ (xs.length:ℝ)^2*δ := by
  induction xs with
  | nil => simp [weighted,comm,Companion.Analytic.comm,hs,hsNorm,hsSquared]
  | cons a xs ih =>
    have hn' : ∀ b ∈ xs, ‖b‖ ≤ 1 := fun b hb => hn b (by simp [hb])
    have hc' : ∀ b ∈ xs, hs (comm b s.xi) ≤ δ := fun b hb => hc b (by simp [hb])
    have hb' : ∀ b ∈ xs, weighted s (comm b Y) ≤ δ := fun b hb => hbase b (by simp [hb])
    rw [List.prod_cons, comm_mul_left]
    calc
      _ ≤ weighted s (a*comm xs.prod Y)+weighted s (comm a Y*xs.prod) := weighted_add _ _ _
      _ ≤ ‖a‖*weighted s (comm xs.prod Y) +
          (‖xs.prod‖*weighted s (comm a Y)+‖comm a Y‖*hs (comm xs.prod s.xi)) :=
        add_le_add (weighted_left _ _ _) (weighted_right _ _ _)
      _ ≤ 1*((xs.length:ℝ)^2*δ)+(1*δ+2*(xs.length*δ)) := by
        gcongr <;> first
        | exact hsNorm_nonneg _
        | exact hn a (by simp)
        | exact ih hn' hc' hb'
        | exact word_norm hd xs hn'
        | exact hbase a (by simp)
        | exact norm_comm_contractions a Y (hn a (by simp)) hY
        | exact word_state_commutator s hd δ hδ xs hn' hc'
      _ = ((a::xs).length:ℝ)^2*δ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem word_word_commutator {d : ℕ} (s : State d) (hd : 0 < d) (δ : ℝ) (hδ : 0 ≤ δ)
    (xs ys : List (Mat d))
    (hnx : ∀ a ∈ xs, ‖a‖ ≤ 1) (hcx : ∀ a ∈ xs, hs (comm a s.xi) ≤ δ)
    (hny : ∀ a ∈ ys, ‖a‖ ≤ 1) (hcy : ∀ a ∈ ys, hs (comm a s.xi) ≤ δ)
    (hbase : ∀ a ∈ xs, ∀ b ∈ ys, weighted s (comm a b) ≤ δ) :
    weighted s (comm xs.prod ys.prod) ≤
      ((ys.length:ℝ)*(xs.length:ℝ)^2+(ys.length:ℝ)^2)*δ := by
  induction ys with
  | nil => simp [weighted,comm,Companion.Analytic.comm,hs,hsNorm,hsSquared]
  | cons b ys ih =>
    have hn' : ∀ a ∈ ys, ‖a‖ ≤ 1 := fun a ha => hny a (by simp [ha])
    have hc' : ∀ a ∈ ys, hs (comm a s.xi) ≤ δ := fun a ha => hcy a (by simp [ha])
    have hb' : ∀ a ∈ xs, ∀ z ∈ ys, weighted s (comm a z) ≤ δ :=
      fun a ha z hz => hbase a ha z (by simp [hz])
    have hsingle := word_single_commutator s hd δ hδ xs b (hny b (by simp)) hnx hcx
      (fun a ha => hbase a ha b (by simp))
    rw [List.prod_cons, comm_mul_right]
    calc
      _ ≤ weighted s (comm xs.prod b*ys.prod)+weighted s (b*comm xs.prod ys.prod) := weighted_add _ _ _
      _ ≤ (‖ys.prod‖*weighted s (comm xs.prod b)+‖comm xs.prod b‖*hs (comm ys.prod s.xi)) +
          ‖b‖*weighted s (comm xs.prod ys.prod) :=
        add_le_add (weighted_right _ _ _) (weighted_left _ _ _)
      _ ≤ (1*((xs.length:ℝ)^2*δ)+2*(ys.length*δ)) +
          1*(((ys.length:ℝ)*(xs.length:ℝ)^2+(ys.length:ℝ)^2)*δ) := by
        gcongr <;> first
        | exact hsNorm_nonneg _
        | exact word_norm hd ys hn'
        | exact hsingle
        | exact norm_comm_contractions xs.prod b (word_norm hd xs hnx) (hny b (by simp))
        | exact word_state_commutator s hd δ hδ ys hn' hc'
        | exact hny b (by simp)
        | exact ih hn' hc' hb'
      _ ≤ (((b::ys).length:ℝ)*(xs.length:ℝ)^2+((b::ys).length:ℝ)^2)*δ := by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith

/-- The word-interchange bound in Lemma 9.3, items (ii) and (v).
This kernel-checked proof contains no spectral functional calculus, so the
cross-clock calculation cannot introduce a product of depth Lipschitz losses. -/
theorem raw_word_interchange {d : ℕ} (s : State d) (hd : 0 < d) (δ : ℝ) (hδ : 0 ≤ δ)
    (xs ys : List (Mat d))
    (hnx : ∀ a ∈ xs, ‖a‖ ≤ 1) (hcx : ∀ a ∈ xs, hs (comm a s.xi) ≤ δ)
    (hny : ∀ a ∈ ys, ‖a‖ ≤ 1) (hcy : ∀ a ∈ ys, hs (comm a s.xi) ≤ δ)
    (hbase : ∀ a ∈ xs, ∀ b ∈ ys, weighted s (comm a b) ≤ δ) :
    weighted s (comm xs.prod ys.prod) ≤
      (xs.length:ℝ)*ys.length*(xs.length+ys.length+1)*δ := by
  by_cases hx : xs=[]
  · subst xs
    simp [weighted,comm,Companion.Analytic.comm,hs,hsNorm,hsSquared]
  have hL : (1:ℝ) ≤ xs.length := by exact_mod_cast List.length_pos_iff.mpr hx
  have hm : (ys.length:ℝ)^2 ≤ (xs.length:ℝ)*(ys.length:ℝ)^2 :=
    by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg (ys.length:ℝ))]
  calc
    _ ≤ ((ys.length:ℝ)*(xs.length:ℝ)^2+(ys.length:ℝ)^2)*δ :=
      word_word_commutator s hd δ hδ xs ys hnx hcx hny hcy hbase
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hδ
      have hprod : (0:ℝ) ≤ (xs.length:ℝ)*(ys.length:ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith

end
end E2
