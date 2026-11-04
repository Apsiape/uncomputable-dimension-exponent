import E2.RecognizerEncoding

namespace E2.RecognizerImplementation
open Turing Turing.PartrecToTM2

def decodePower (n : ℕ) : Part ℕ :=
  Nat.rfind (fun e => Part.some (decide ((2:ℕ)^e = n)))

theorem decodePower_pow (e : ℕ) : decodePower (2^e) = Part.some e := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  refine ⟨by simp,?_⟩
  intro m hm
  have hne : (2:ℕ)^m ≠ 2^e := ne_of_lt (Nat.pow_lt_pow_right (by decide) hm)
  simp [hne]

theorem power_primrec : Primrec (fun e : ℕ => (2:ℕ)^e) := by
  apply Primrec.nat_iff.mpr
  exact (Nat.Primrec.pow.comp ((Nat.Primrec.const 2).pair Nat.Primrec.id)).of_eq
    (fun n => by simp)

theorem decodePower_partrec : Partrec decodePower := by
  have hp : Primrec (fun p : ℕ × ℕ => decide ((2:ℕ)^p.2 = p.1)) :=
    Primrec.eq.decide.comp (power_primrec.comp Primrec.snd) Primrec.fst
  exact Partrec.rfind hp.to_comp.partrec.to₂

def universal (n : ℕ) : Part ℕ :=
  (decodePower n).bind (fun e => Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) 0)

theorem universal_partrec : Partrec universal := by
  have he : Computable Nat.Partrec.Code.ofNatCode := by
    simpa only [Nat.Partrec.Code.ofNatCode_eq] using (Primrec.ofNat Nat.Partrec.Code).to_comp
  exact Partrec.bind decodePower_partrec
    (Nat.Partrec.Code.eval_part.comp (he.comp Computable.snd) (Computable.const 0))

theorem universal_pow (e : ℕ) : universal (2^e) =
    Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) 0 := by
  simp [universal,decodePower_pow]

theorem universal_code : ∃ c : ToPartrec.Code,
    ∀ e, (c.eval [2^e]).Dom ↔ e ∈ haltingSet := by
  obtain ⟨c,hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr universal_partrec)
  refine ⟨c,?_⟩
  intro e
  have h := hc ⟨[2^e],rfl⟩
  change c.eval [2^e] = (List.singleton <$> universal (2^e)) at h
  simpa [universal_pow,haltingSet] using congrArg Part.Dom h

end E2.RecognizerImplementation