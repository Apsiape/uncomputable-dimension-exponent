import E2.CantorDefinitions
import E2.Weighted
import Mathlib.Analysis.SpecificLimits.Normed

namespace E2
noncomputable section
open scoped BigOperators

def cantorWeight (j : ℕ) : ℝ := (1/4:ℝ)^j
def cantorTerm (b : ℕ → Bool) (j : ℕ) : ℝ :=
  if b j then (3/4:ℝ)*cantorWeight j else 0
def dropBits (b : ℕ → Bool) (j : ℕ) : ℕ → Bool := fun n => b (n+j)

theorem cantorWeight_zpow (j : ℕ) : cantorWeight j = (4:ℝ)^(-(j:ℤ)) := by
  simp [cantorWeight, zpow_neg, inv_pow]

theorem cantorWeight_nonneg (j : ℕ) : 0 ≤ cantorWeight j := by
  unfold cantorWeight
  positivity

theorem cantorWeight_pos (j : ℕ) : 0 < cantorWeight j := by
  unfold cantorWeight
  positivity

theorem cantorWeight_succ (j : ℕ) : cantorWeight (j+1) = (1/4)*cantorWeight j := by
  simp [cantorWeight, pow_succ, mul_comm]

theorem cantorTerm_bounds (b : ℕ → Bool) (j : ℕ) :
    0 ≤ cantorTerm b j ∧ cantorTerm b j ≤ (3/4)*cantorWeight j := by
  unfold cantorTerm
  have hw := cantorWeight_nonneg j
  split <;> constructor <;> first | positivity | exact le_rfl

theorem cantorTerm_summable (b : ℕ → Bool) : Summable (cantorTerm b) := by
  apply Summable.of_nonneg_of_le (fun j => (cantorTerm_bounds b j).1)
    (fun j => (cantorTerm_bounds b j).2)
  exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)).mul_left (3/4)

theorem cantorCoordinate_eq_tsum (b : ℕ → Bool) :
    cantorCoordinate b = ∑' j, cantorTerm b j := by
  apply tsum_congr
  intro j
  unfold cantorTerm cantorWeight
  split <;> simp_all [zpow_neg, zpow_add₀, pow_succ, inv_pow]
  ring

theorem cantorCoordinate_bounds (b : ℕ → Bool) :
    0 ≤ cantorCoordinate b ∧ cantorCoordinate b ≤ 1 := by
  rw [cantorCoordinate_eq_tsum]
  constructor
  · exact tsum_nonneg (fun j => (cantorTerm_bounds b j).1)
  · calc
      _ ≤ ∑' j, (3/4:ℝ)*cantorWeight j :=
        (cantorTerm_summable b).tsum_le_tsum (fun j => (cantorTerm_bounds b j).2)
          ((summable_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)).mul_left (3/4))
      _ = 1 := by
        unfold cantorWeight
        rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)]
        norm_num

theorem cantorCoordinate_zero : cantorCoordinate (fun _ => false) = 0 := by
  simp [cantorCoordinate]

theorem cantorCoordinate_one : cantorCoordinate (fun _ => true) = 1 := by
  rw [cantorCoordinate_eq_tsum]
  simp only [cantorTerm, Bool.true_eq, reduceIte, cantorWeight]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)]
  norm_num

theorem cantorCoordinate_head (b : ℕ → Bool) :
    cantorCoordinate b = (if b 0 then (3/4:ℝ) else 0) +
      (1/4)*cantorCoordinate (dropBits b 1) := by
  rw [cantorCoordinate_eq_tsum, (cantorTerm_summable b).tsum_eq_zero_add,
    cantorCoordinate_eq_tsum, ← tsum_mul_left]
  congr 1
  · simp [cantorTerm,cantorWeight]
  · apply tsum_congr
    intro j
    change (if b (j+1) then (3/4:ℝ)*cantorWeight (j+1) else 0) =
      (1/4)*(if b (j+1) then (3/4:ℝ)*cantorWeight j else 0)
    rw [cantorWeight_succ]
    split <;> ring

theorem cantorCoordinate_prefix_difference (b c : ℕ → Bool) (j : ℕ)
    (h : ∀ k < j, b k=c k) :
    cantorCoordinate b-cantorCoordinate c =
      cantorWeight j*(cantorCoordinate (dropBits b j)-cantorCoordinate (dropBits c j)) := by
  induction j generalizing b c with
  | zero =>
    change cantorCoordinate b-cantorCoordinate c = 1*(cantorCoordinate b-cantorCoordinate c)
    ring
  | succ j ih =>
    have h0 : b 0=c 0 := h 0 (by omega)
    have ht : ∀ k<j, dropBits b 1 k=dropBits c 1 k := fun k hk => h (k+1) (by omega)
    have hi := ih (dropBits b 1) (dropBits c 1) ht
    rw [cantorCoordinate_head b,cantorCoordinate_head c,h0,cantorWeight_succ]
    have hb : dropBits (dropBits b 1) j = dropBits b (j+1) := by
      funext n
      simp [dropBits,Nat.add_assoc]
    have hc : dropBits (dropBits c 1) j = dropBits c (j+1) := by
      funext n
      simp [dropBits,Nat.add_assoc]
    rw [hb,hc] at hi
    nlinarith

theorem cantorCoordinate_prefix_bound (b c : ℕ → Bool) (j : ℕ)
    (h : ∀ k < j, b k=c k) :
    |cantorCoordinate b-cantorCoordinate c| ≤ cantorWeight j := by
  rw [cantorCoordinate_prefix_difference b c j h,abs_mul,abs_of_nonneg (cantorWeight_nonneg j)]
  have hb := cantorCoordinate_bounds (dropBits b j)
  have hc := cantorCoordinate_bounds (dropBits c j)
  have : |cantorCoordinate (dropBits b j)-cantorCoordinate (dropBits c j)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  simpa using mul_le_mul_of_nonneg_left this (cantorWeight_nonneg j)

theorem cantorCoordinate_first_difference (b c : ℕ → Bool) (j : ℕ)
    (h : ∀ k < j, b k=c k) (hne : b j≠c j) :
    (1/2)*cantorWeight j ≤ |cantorCoordinate b-cantorCoordinate c| := by
  rw [cantorCoordinate_prefix_difference b c j h,abs_mul,abs_of_nonneg (cantorWeight_nonneg j)]
  have hb := cantorCoordinate_bounds (dropBits (dropBits b j) 1)
  have hc := cantorCoordinate_bounds (dropBits (dropBits c j) 1)
  have hgap : (1/2:ℝ) ≤ |cantorCoordinate (dropBits b j)-cantorCoordinate (dropBits c j)| := by
    rw [cantorCoordinate_head (dropBits b j),cantorCoordinate_head (dropBits c j)]
    simp only [dropBits,Nat.zero_add] at *
    cases hb0 : b j <;> cases hc0 : c j <;> simp_all
    · rw [abs_of_nonpos] <;> linarith
    · rw [abs_of_nonneg] <;> linarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hgap (cantorWeight_nonneg j)

theorem cantorCoordinate_injective : Function.Injective cantorCoordinate := by
  intro b c hbc
  by_contra hne
  have hex : ∃ j, b j≠c j := by
    by_contra hn
    apply hne
    funext j
    simpa using not_exists.mp hn j
  let j := Nat.find hex
  have hd := cantorCoordinate_first_difference b c j
    (fun k hk => by simpa using Nat.find_min hex hk) (Nat.find_spec hex)
  rw [hbc,sub_self,abs_zero] at hd
  have := cantorWeight_pos j
  linarith

end
end E2
