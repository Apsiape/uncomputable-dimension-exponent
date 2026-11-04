import E2.FiniteSlotAllocation
import Mathlib.Data.Nat.Periodic

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators

def residueCount (x N a d : ℕ) : ℕ :=
  ((Finset.Ico x (x+N)).filter (fun y => y % d = a)).card

theorem residueCount_add (x M N a d : ℕ) :
    residueCount x (M+N) a d =
      residueCount x M a d + residueCount (x+M) N a d := by
  unfold residueCount
  rw [show x+(M+N)=(x+M)+N by omega,
    ←Finset.Ico_union_Ico_eq_Ico (show x ≤ x+M by omega)
      (show x+M ≤ x+M+N by omega),Finset.filter_union,Finset.card_union_of_disjoint]
  exact (Finset.Ico_disjoint_Ico_consecutive _ _ _).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem residueCount_period (x a d : ℕ) (ha : a < d) :
    residueCount x d a d = 1 := by
  rw [residueCount,Nat.filter_Ico_card_eq_of_periodic]
  · rw [Nat.count_eq_card_filter_range]
    have he : (Finset.range d).filter (fun y => y%d=a) = {a} := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
      constructor
      · rintro ⟨hy,hmod⟩
        rwa [Nat.mod_eq_of_lt hy] at hmod
      · intro h
        subst y
        exact ⟨ha,Nat.mod_eq_of_lt ha⟩
    rw [he,Finset.card_singleton]
  · intro y
    simp only [Nat.add_mod_right]

theorem residueCount_mono (x a d : ℕ) {M N : ℕ} (h : M ≤ N) :
    residueCount x M a d ≤ residueCount x N a d := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro y hy
  simp only [Finset.mem_Ico] at hy ⊢
  omega

theorem residueCount_multiple (x a d q : ℕ) (ha : a < d) :
    residueCount x (q*d) a d = q := by
  induction q with
  | zero => simp [residueCount]
  | succ q ih =>
    rw [Nat.succ_mul,residueCount_add,ih,residueCount_period _ _ _ ha]

/-- A complete one-residue interval estimate, uniform in its starting point. -/
theorem residueCount_discrepancy (x N a d : ℕ) (ha : a < d) :
    |(residueCount x N a d : ℝ) - (N:ℝ)/(d:ℝ)| ≤ 1 := by
  have hd : 0 < d := by omega
  have hdecomp := Nat.mod_add_div N d
  have hrem := Nat.mod_lt N hd
  have hlo : N/d*d ≤ N := Nat.div_mul_le_self N d
  have hhi : N ≤ (N/d+1)*d := by nlinarith
  have hclo := residueCount_mono x a d hlo
  have hchi := residueCount_mono x a d hhi
  rw [residueCount_multiple _ _ _ _ ha] at hclo hchi
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hcloR : (N/d:ℕ) ≤ (residueCount x N a d:ℝ) := by exact_mod_cast hclo
  have hchiR : (residueCount x N a d:ℝ) ≤ (N/d:ℕ)+1 := by exact_mod_cast hchi
  have hdecompR : (N%d:ℕ)+(d:ℝ)*(N/d:ℕ) = N := by exact_mod_cast hdecomp
  have hremR : (N%d:ℕ) < (d:ℝ) := by exact_mod_cast hrem
  have hrem0 : (0:ℝ) ≤ (N%d:ℕ) := by positivity
  apply abs_le.mpr
  constructor
  · have : (N:ℝ)/(d:ℝ) ≤ (N/d:ℕ)+1 := by
      apply (div_le_iff₀ hdR).mpr
      nlinarith
    linarith
  · have : (N/d:ℕ) ≤ (N:ℝ)/(d:ℝ) := by
      apply (le_div_iff₀ hdR).mpr
      nlinarith
    linarith

end
end E2.FiniteConstruction
