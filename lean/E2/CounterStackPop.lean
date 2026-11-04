import E2.CounterStack

namespace E2.CounterStack
open CounterFlow Function Relation
variable {r B : ℕ} {Q : Type*}
variable (hB : 0 < B) (M : Q → Macro r B Q)

theorem div_correct (i : Fin r) (f : Fin B → Q) (peek : Bool)
    (v : Fin r → ℕ) (n m : ℕ) (a : Fin B) :
    Reach hB M (some (.div i f peek a),put v i n m)
      (some (.out i f peek ⟨(a.val+n)%B,Nat.mod_lt _ hB⟩),
        put v i 0 (m+(a.val+n)/B)) := by
  induction n generalizing a m with
  | zero =>
    simpa [Nat.mod_eq_of_lt a.isLt,Nat.div_eq_of_lt a.isLt] using
      one hB M (a := (some (.div i f peek a),put v i 0 m))
        (b := (some (.out i f peek a),put v i 0 m)) (by simp [step,table])
  | succ n ih =>
    by_cases ha : a.val+1 < B
    · have h := one hB M (a := (some (.div i f peek a),put v i (n+1) m))
        (b := (some (.div i f peek ⟨a.val+1,ha⟩),put v i n m))
        (by simp [step,table,ha])
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.trans (ih m ⟨a.val+1,ha⟩)
    · have he : a.val+(n+1) = B+n := by omega
      have h := one hB M (a := (some (.div i f peek a),put v i (n+1) m))
        (b := (some (.carry i f peek),put v i n m))
        (by simp [step,table,ha])
      have hh := one hB M (a := (some (.carry i f peek),put v i n m))
        (b := (some (.div i f peek ⟨0,hB⟩),put v i n (m+1)))
        (by simp [step,table])
      simpa [he,Nat.add_mod,Nat.add_div_left _ hB,Nat.ne_of_gt hB,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using h.trans (hh.trans (ih (m+1) ⟨0,hB⟩))

theorem out_correct (i : Fin r) (f : Fin B → Q) (peek : Bool)
    (a : Fin B) (v : Fin r → ℕ) (n m : ℕ) :
    Reach hB M (some (.out i f peek a),put v i n m)
      (some (if peek then .mul i a (f a) else .run (f a)),put v i (n+m) 0) := by
  induction m generalizing n with
  | zero => exact one hB M (by simp [step,table])
  | succ m ih =>
    have h := one hB M (a := (some (.out i f peek a),put v i n (m+1)))
      (b := (some (.outInc i f peek a),put v i n m))
      (by simp [step,table])
    have hh := one hB M (a := (some (.outInc i f peek a),put v i n m))
      (b := (some (.out i f peek a),put v i (n+1) m))
      (by simp [step,table])
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.trans (hh.trans (ih (n+1)))

theorem pop_correct (i : Fin r) (f : Fin B → Q) (v : Fin r → ℕ) :
    Reach hB M (some (.div i f false ⟨0,hB⟩),Fin.snoc v 0)
      (some (.run (f ⟨v i%B,Nat.mod_lt _ hB⟩)),Fin.snoc (update v i (v i/B)) 0) := by
  have h := div_correct hB M i f false v (v i) 0 ⟨0,hB⟩
  have hh := out_correct hB M i f false ⟨v i%B,Nat.mod_lt _ hB⟩ v 0 (v i/B)
  simp only [Nat.zero_add,Bool.false_eq_true,↓reduceIte] at h hh
  simpa [put] using h.trans hh

theorem peek_correct (i : Fin r) (f : Fin B → Q) (v : Fin r → ℕ) :
    Reach hB M (some (.div i f true ⟨0,hB⟩),Fin.snoc v 0)
      (some (.run (f ⟨v i%B,Nat.mod_lt _ hB⟩)),Fin.snoc v 0) := by
  have h := div_correct hB M i f true v (v i) 0 ⟨0,hB⟩
  have hh := out_correct hB M i f true ⟨v i%B,Nat.mod_lt _ hB⟩ v 0 (v i/B)
  simp only [Nat.zero_add,↓reduceIte] at h hh
  have hhh := push_correct hB M i ⟨v i%B,Nat.mod_lt _ hB⟩
    (f ⟨v i%B,Nat.mod_lt _ hB⟩) (update v i (v i/B))
  simp only [Function.update_self] at hhh
  have he : B*(v i/B)+v i%B = v i := Nat.div_add_mod (v i) B
  simpa [put,he,Function.update_idem] using (h.trans hh).trans hhh

end E2.CounterStack