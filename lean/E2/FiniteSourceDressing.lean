import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section

/-- The source tuple's actual dressed address increment is ordinary binary
increment with a single, fixed optional permutation at the all-ones boundary. -/
theorem address_dressed_increment (p : CounterProgram) (N k : ℕ) :
    (addressDressing p N k).trans
      ((addressForward p N k).trans (addressDressing p N k).symm) =
      twistedIncrement N (((rotateWord k).symm)^flagPrefix (finiteMask p N) (2^N)) := by
  apply Equiv.ext
  rintro ⟨a,b⟩
  change (addressDressing p N k).symm
    (addressForward p N k (addressDressing p N k (a,b))) = _
  rw [addressDressing,addressForward,dressing_gauge]
  have hi : (incrementWord N a).val=listIncrement a.val := rfl
  change (incrementWord N a,
    (((rotateWord k).symm) ^
      (flagPrefix (finiteMask p N) (listNumber a.val)+(if finiteMask p N (listNumber a.val) then 1 else 0)-
        flagPrefix (finiteMask p N) (listNumber (incrementWord N a).val))) b) =
    (incrementWord N a,
      ((((rotateWord k).symm)^flagPrefix (finiteMask p N) (2^N)) ^
        (if a.val.all id then 1 else 0 : ℤ)) b)
  rw [hi,listNumber_increment]
  by_cases hall : a.val.all id=true
  · simp only [hall,↓reduceIte,flagPrefix_zero,sub_zero,zpow_one]
    have hn : listNumber a.val+1=2^N := by simpa only [a.property] using listNumber_all_ones a.val hall
    rw [←flagPrefix_succ,hn]
  · simp [hall,flagPrefix_succ]

end
end E2.FiniteConstruction