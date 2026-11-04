import E2.FiniteWindowDiscrepancy
import E2.FiniteCutoff

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def addressClass (x e : ℕ) : Prop := x % 4^(e+1) = 4^e

theorem addressClass_unique {x e j : ℕ} (he : addressClass x e)
    (hj : addressClass x j) : e = j := by
  suffices hnot : ∀ e j, e < j → addressClass x e → ¬addressClass x j by
    rcases lt_trichotomy e j with h|h|h
    · exact False.elim (hnot e j h he hj)
    · exact h
    · exact False.elim (hnot j e h hj he)
  intro e j hej he hj
  have hd : 4^(e+1) ∣ 4^(j+1) := pow_dvd_pow 4 (by omega)
  have hd' : 4^(e+1) ∣ 4^j := pow_dvd_pow 4 hej
  have hm := Nat.mod_mod_of_dvd x hd
  rw [hj,Nat.mod_eq_zero_of_dvd hd',he] at hm
  have hpos : 0 < 4^e := by positivity
  omega

theorem addressClass_divisible {x e m : ℕ} (hm : m < e)
    (he : addressClass x e) : 4^(m+1) ∣ x := by
  have hd : 4^(m+1) ∣ 4^(e+1) := pow_dvd_pow 4 (by omega)
  have hd' : 4^(m+1) ∣ 4^e := pow_dvd_pow 4 hm
  apply Nat.dvd_of_mod_eq_zero
  rw [←Nat.mod_mod_of_dvd x hd,he,Nat.mod_eq_zero_of_dvd hd']

def finiteMask (p : CounterProgram) (N x : ℕ) : Bool :=
  decide (∃ e ∈ Finset.range (N/2), detected p e N ∧ addressClass x e)

def maskIndices (p : CounterProgram) (N : ℕ) : Finset ℕ :=
  (Finset.range (N/2)).filter (fun e => detected p e N)

def maskDensity (S : Finset ℕ) : ℝ := ∑ e ∈ S, (1/4:ℝ)^(e+1)

def maskWindow (S : Finset ℕ) (x N : ℕ) : ℕ :=
  ∑ e ∈ S, residueCount x N (4^e) (4^(e+1))

theorem classIndicator_sum_le_one (S : Finset ℕ) (x : ℕ) :
    (∑ e ∈ S, if addressClass x e then 1 else 0 : ℕ) ≤ 1 := by
  by_cases h : ∃ e ∈ S, addressClass x e
  · obtain ⟨e,he,hclass⟩ := h
    rw [Finset.sum_eq_single e]
    · simp [hclass]
    · intro j hj hne
      simp only [ite_eq_right_iff]
      intro hjclass
      exact False.elim (hne (addressClass_unique hjclass hclass))
    · exact fun hnot => False.elim (hnot he)
  · have hz : ∀ e ∈ S, ¬addressClass x e := by simpa only [not_exists,not_and] using h
    exact (Finset.sum_eq_zero (fun e he => if_neg (hz e he))).le.trans (by omega)

theorem maskWindow_sum (S : Finset ℕ) (x N : ℕ) :
    maskWindow S x N = ∑ y ∈ Finset.Ico x (x+N),
      ∑ e ∈ S, if addressClass y e then 1 else 0 := by
  unfold maskWindow residueCount
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro e he
  by_cases h : addressClass y e <;> simp_all only [addressClass, ite_true, ite_false]

/-- All classes beyond the cutoff together have at most one hit in a short
window. Bounding each of them separately would lose the logarithmic estimate. -/
theorem maskWindow_tail_le_one (S : Finset ℕ) (x N m : ℕ)
    (hS : ∀ e ∈ S, m < e) (hN : N ≤ 4^(m+1)) : maskWindow S x N ≤ 1 := by
  rw [maskWindow_sum]
  calc
    _ ≤ ∑ y ∈ Finset.Ico x (x+N), if y % 4^(m+1)=0 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hd : y % 4^(m+1)=0
      · simpa [hd] using classIndicator_sum_le_one S y
      · have hz : ∀ e ∈ S, ¬addressClass y e := by
          intro e he hc
          exact hd (Nat.mod_eq_zero_of_dvd (addressClass_divisible (hS e he) hc))
        rw [if_neg hd, Finset.sum_eq_zero (fun e he => if_neg (hz e he))]
    _ = residueCount x N 0 (4^(m+1)) := by simp [residueCount,Finset.sum_boole]
    _ ≤ residueCount x (4^(m+1)) 0 (4^(m+1)) := residueCount_mono _ _ _ hN
    _ = 1 := residueCount_period _ _ _ (by positivity)

theorem maskWindow_discrepancy_sum (S : Finset ℕ) (x N : ℕ) :
    |(maskWindow S x N:ℝ) - N*maskDensity S| ≤ S.card := by
  have he : (maskWindow S x N:ℝ) - N*maskDensity S =
      ∑ e ∈ S, ((residueCount x N (4^e) (4^(e+1)):ℝ)-N/(4^(e+1):ℕ)) := by
    simp only [maskWindow,maskDensity,Nat.cast_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    congr 1
    simp [div_eq_mul_inv,inv_pow]
  rw [he]
  calc
    _ ≤ ∑ e ∈ S, |(residueCount x N (4^e) (4^(e+1)):ℝ)-N/(4^(e+1):ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ S, (1:ℝ) := Finset.sum_le_sum (fun e _ =>
      residueCount_discrepancy x N (4^e) (4^(e+1)) (by
        exact Nat.pow_lt_pow_succ (by norm_num : 1 < (4:ℕ))))
    _ = S.card := by simp

end
end E2.FiniteConstruction
