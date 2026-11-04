import E2.FiniteSourceHistories

namespace E2.FiniteConstruction
noncomputable section

theorem binaryDecode_accepted (bs : List Bool) (e : ℕ) (h : binaryDecode bs=some (e,true)) :
    2*e+2 ≤ bs.length ∧ addressClass (listNumber bs) e := by
  induction bs using List.twoStepInduction generalizing e with
  | nil => simp [binaryDecode] at h
  | singleton b => simp [binaryDecode] at h
  | cons_cons b c bs ih _ =>
    cases b <;> cases c
    · have hm : (binaryDecode bs).map (fun z => (z.1+1,z.2))=some (e,true) := by
        simpa only [binaryDecode,Bool.false_or,Bool.false_eq_true,↓reduceIte] using h
      obtain ⟨⟨d,b⟩,hd,he⟩ := Option.map_eq_some_iff.mp hm
      have he1 : d+1=e := congrArg Prod.fst he
      have he2 : b=true := congrArg Prod.snd he
      subst e
      subst b
      obtain ⟨hlen,hclass⟩ := ih d hd
      constructor
      · simp only [List.length_cons]; omega
      · have hn : listNumber (false::false::bs)=4*listNumber bs := by simp only [listNumber]; ring
        unfold addressClass at hclass ⊢
        rw [hn,show 4^(d+1+1)=4*4^(d+1) by rw [pow_succ]; ring,
          Nat.mul_mod_mul_left,hclass,pow_succ]
        omega
    · simp [binaryDecode] at h
    · have he : some (0,true)=some (e,true) := by simpa [binaryDecode] using h
      have he0 : 0=e := congrArg Prod.fst (Option.some.inj he)
      subst e
      constructor
      · simp
      · simp only [addressClass,listNumber,pow_one,pow_zero]
        omega
    · simp [binaryDecode] at h

theorem historyInitial_idle (p : CounterProgram) (bs : List Bool)
    (hL : decodedL bs=false) (t : ℕ) :
    ((p.step)^[t] (historyInitial p bs)).control=p.idle := by
  have hc : (historyInitial p bs).control=p.idle := by
    change (if decodedL bs then p.start else p.idle)=p.idle
    rw [hL]
    rfl
  have hs : p.step (historyInitial p bs)=historyInitial p bs := by
    simp only [CounterProgram.step,hc,p.idle_absorbing]
  have he : (p.step)^[t] (historyInitial p bs)=historyInitial p bs := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply',ih,hs]
  rw [he,hc]

/-- A halt anywhere in the simultaneous diagonal histories is flagged by the
same finite mask used for the optional slots. No recognizer premise is needed. -/
theorem sourceHistory_halt_flag (p : CounterProgram) (N : ℕ) (b q t : BinaryWord N)
    (hhalt : (historyConfig p b.val q.val t.val).control=p.halt) : wordMask p N b=true := by
  by_cases hL : decodedL b.val=true
  · cases hd : binaryDecode b.val with
    | none => simp [decodedL,hd] at hL
    | some z =>
      rcases z with ⟨e,f⟩
      have hf : f=true := by simpa only [decodedL,hd,Option.getD_some] using hL
      subst f
      obtain ⟨hlen,hclass⟩ := binaryDecode_accepted b.val e hd
      have he : e<N/2 := by rw [b.property] at hlen; omega
      have hi : historyInitial p b.val=p.initial e := by
        simp only [historyInitial,hd,Option.getD_some,↓reduceIte]
        rfl
      have hperiod : leadingOnes q.val≤N := by simpa only [q.property] using leadingOnes_le q.val
      have htime : listNumber t.val % 2^leadingOnes q.val < 2^N :=
        (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by omega) hperiod)
      change finiteMask p N (listNumber b.val)=true
      simp only [finiteMask,decide_eq_true_eq]
      refine ⟨e,Finset.mem_range.mpr he,?_,hclass⟩
      refine ⟨listNumber t.val % 2^leadingOnes q.val,htime,?_⟩
      simpa only [historyConfig,cyclicHistory,hi] using hhalt
  · have hfalse : decodedL b.val=false := Bool.eq_false_iff.mpr hL
    have hi := historyInitial_idle p b.val hfalse (listNumber t.val % 2^leadingOnes q.val)
    change ((p.step)^[listNumber t.val % 2^leadingOnes q.val] (historyInitial p b.val)).control=p.halt at hhalt
    exact False.elim (p.distinct.2.2 (hi.symm.trans hhalt))

end
end E2.FiniteConstruction