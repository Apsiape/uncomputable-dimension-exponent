import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section

theorem even_mod_power (n k : ℕ) : (2*n)%2^(k+1)=0 ↔ n%2^k=0 := by
  simp only [←Nat.dvd_iff_mod_eq_zero]
  rw [pow_succ,Nat.mul_comm (2^k) 2,Nat.mul_dvd_mul_iff_left (by omega : 0<2)]

theorem odd_mod_power (n k : ℕ) : (1+2*n)%2^(k+1)≠0 := by
  intro h
  have hd : 2 ∣ 2^(k+1) := dvd_pow_self 2 (by omega)
  have hdiv : 2 ∣ 1+2*n := hd.trans (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  norm_num [Nat.add_mod,Nat.mul_mod] at hm

/-- The reset predicate used by the source tuple is exactly congruence to zero
at the fuel-selected period, including all-ones fuel. -/
theorem listReset_eq_mod (qs ts : List Bool) (hlen : qs.length=ts.length) :
    listReset qs ts = decide (listNumber ts % 2^leadingOnes qs=0) := by
  induction qs generalizing ts with
  | nil => simp [listReset,leadingOnes,Nat.mod_one]
  | cons q qs ih =>
    cases ts with
    | nil => simp at hlen
    | cons t ts =>
      have hl : qs.length=ts.length := by simpa using hlen
      cases q
      · simp [listReset,leadingOnes,Nat.mod_one]
      · have hp : leadingOnes (true::qs)=leadingOnes qs+1 := by simp [leadingOnes]
        cases t
        · simp only [listReset,Bool.not_false,Bool.true_and,hp,listNumber,even_mod_power]
          exact ih ts hl
        · simp [listReset,hp,listNumber,odd_mod_power]

theorem leadingOnes_le (qs : List Bool) : leadingOnes qs ≤ qs.length := by
  induction qs with
  | nil => simp [leadingOnes]
  | cons q qs ih => cases q <;> simp [leadingOnes] at * <;> omega

theorem fuelPeriod_dvd (N : ℕ) (q : BinaryWord N) : 2^leadingOnes q.val ∣ 2^N :=
  pow_dvd_pow 2 (by simpa only [q.property] using leadingOnes_le q.val)

theorem wordNumber_increment_mod (N : ℕ) (t : BinaryWord N) :
    listNumber (incrementWord N t).val=(listNumber t.val+1)%2^N := by
  have h := congrArg Fin.val (wordNumber_increment N t)
  rw [finRotate_apply] at h
  change listNumber (incrementWord N t).val=(listNumber t.val+(1%2^N))%2^N at h
  simpa only [Nat.add_mod,Nat.mod_mod] using h

/-- Actual simultaneous computation history across every cyclic time boundary. -/
theorem sourceHistory_transition (p : CounterProgram) (N : ℕ)
    (b q t : BinaryWord N) :
    historyConfig p b.val q.val (incrementWord N t).val =
      if listReset q.val (incrementWord N t).val then historyInitial p b.val
      else p.step (historyConfig p b.val q.val t.val) := by
  have hl : q.val.length=(incrementWord N t).val.length :=
    q.property.trans (incrementWord N t).property.symm
  rw [listReset_eq_mod _ _ hl]
  simp only [decide_eq_true_eq]
  unfold historyConfig
  rw [wordNumber_increment_mod]
  exact cyclicHistory_transition p.step (historyInitial p b.val)
    (2^leadingOnes q.val) (2^N) (listNumber t.val) (by positivity) (fuelPeriod_dvd N q)

theorem sourceHistory_initial (p : CounterProgram) (N : ℕ)
    (b q t : BinaryWord N) (hreset : listReset q.val t.val=true) :
    historyConfig p b.val q.val t.val=historyInitial p b.val := by
  rw [listReset_eq_mod _ _ (q.property.trans t.property.symm),decide_eq_true_eq] at hreset
  exact cyclicHistory_reset _ _ hreset

end
end E2.FiniteConstruction