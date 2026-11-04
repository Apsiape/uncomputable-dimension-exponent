import E2.FiniteBitClock
import E2.Program

namespace E2.FiniteConstruction
noncomputable section

def cyclicHistory {α : Type*} (step : α → α) (initial : α) (period t : ℕ) : α :=
  step^[t % period] initial

theorem cyclicHistory_reset {α : Type*} (step : α → α) (initial : α)
    {period t : ℕ} (ht : t % period = 0) :
    cyclicHistory step initial period t = initial := by
  simp [cyclicHistory,ht]

theorem successor_mod {period t : ℕ} (hperiod : 0 < period)
    (hn : (t+1)%period ≠ 0) : (t+1)%period = t%period+1 := by
  have hlt := Nat.mod_lt t hperiod
  have hle : t%period+1 ≤ period := by omega
  have hne : t%period+1 ≠ period := by
    intro he
    apply hn
    rw [Nat.add_mod,show 1%period=1%period by rfl,←Nat.add_mod]
    have hx : (t%period+1)%period=0 := by rw [he,Nat.mod_self]
    simpa only [Nat.add_mod,Nat.mod_mod] using hx
  have heq : (t+1)%period=(t%period+1)%period := by
    simp only [Nat.add_mod,Nat.mod_mod]
  rw [heq,Nat.mod_eq_of_lt (by omega)]

theorem cyclicHistory_step {α : Type*} (step : α → α) (initial : α)
    {period t : ℕ} (hp : 0 < period) (ht : (t+1)%period ≠ 0) :
    cyclicHistory step initial period (t+1) = step (cyclicHistory step initial period t) := by
  unfold cyclicHistory
  rw [successor_mod hp ht,Function.iterate_succ_apply']

/-- Reset and deterministic transition hold at the cyclic time boundary too,
provided the reset period divides the time-register period. -/
theorem cyclicHistory_transition {α : Type*} (step : α → α) (initial : α)
    (period timePeriod t : ℕ) (hp : 0 < period) (hd : period ∣ timePeriod) :
    cyclicHistory step initial period ((t+1)%timePeriod) =
      if ((t+1)%timePeriod)%period=0 then initial
      else step (cyclicHistory step initial period t) := by
  have hm := Nat.mod_mod_of_dvd (t+1) hd
  unfold cyclicHistory at *
  rw [hm]
  split_ifs with h
  · simp [h]
  · rw [successor_mod hp h,Function.iterate_succ_apply']

def counterCoordinate (n : ℕ) : ℝ := (1/2:ℝ)^n
def counterZero (n : ℕ) : ℝ := if n=0 then 1 else 0
def counterWitness (n : ℕ) : ℝ := if n=0 then 0 else 2*counterCoordinate n

theorem counterCoordinate_bounds (n : ℕ) :
    0 ≤ counterCoordinate n ∧ counterCoordinate n ≤ 1 := by
  unfold counterCoordinate
  exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem counterWitness_bounds (n : ℕ) :
    0 ≤ counterWitness n ∧ counterWitness n ≤ 1 := by
  cases n with
  | zero => norm_num [counterWitness]
  | succ n =>
    have h := counterCoordinate_bounds n
    simp only [counterWitness,Nat.add_one_ne_zero,↓reduceIte,counterCoordinate,pow_succ]
    change 0 ≤ 2*((1/2:ℝ)^n*(1/2)) ∧ 2*((1/2:ℝ)^n*(1/2)) ≤ 1
    simp only [counterCoordinate] at h
    constructor <;> nlinarith [h.1,h.2]

theorem counter_zero_test (n : ℕ) :
    counterCoordinate n = counterZero n + (1/2:ℝ)*(1-counterZero n)*counterWitness n := by
  by_cases hn : n=0
  · simp [counterCoordinate,counterZero,counterWitness,hn]
  · simp [counterZero,counterWitness,hn]

theorem counterCoordinate_succ (n : ℕ) :
    counterCoordinate (n+1) = (1/2:ℝ)*counterCoordinate n := by
  simp only [counterCoordinate,pow_succ]
  ring

theorem counterCoordinate_pred {n : ℕ} (hn : n≠0) :
    counterCoordinate (n-1) = 2*counterCoordinate n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.succ_sub_one,counterCoordinate_succ]
  ring

end
end E2.FiniteConstruction
