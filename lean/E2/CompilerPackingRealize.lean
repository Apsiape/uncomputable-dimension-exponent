import E2.CompilerFrameRealize

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial

variable {κ : Type*}

theorem denominator_pos (ws : CompilerWords.WordSum κ) : 0 < denominator ws := by
  unfold denominator
  apply List.prod_pos
  intro a ha
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
  exact t.1.den_pos

theorem denominator_divisible (ws : CompilerWords.WordSum κ) (t : ℚ × List κ) (ht : t ∈ ws) :
    t.1.den ∣ denominator ws :=
  List.dvd_prod (List.mem_map.mpr ⟨t,ht,rfl⟩)

theorem denominator_clears (ws : CompilerWords.WordSum κ) (t : ℚ × List κ) (ht : t ∈ ws) :
    ((((denominator ws : ℤ)*t.1.num) / (t.1.den : ℤ) : ℤ) : ℚ)=
      (denominator ws : ℚ)*t.1 := by
  have hd : (t.1.den : ℤ) ∣ (denominator ws : ℤ)*t.1.num :=
    dvd_mul_of_dvd_left (by exact_mod_cast denominator_divisible ws t ht) _
  have hi := Int.ediv_mul_cancel hd
  have hq : (((((denominator ws : ℤ)*t.1.num) / (t.1.den : ℤ) : ℤ) : ℚ))*(t.1.den:ℚ)=
      (denominator ws:ℚ)*(t.1.num:ℚ) := by exact_mod_cast hi
  apply (mul_right_cancel₀ (show (t.1.den:ℚ) ≠ 0 by exact_mod_cast t.1.den_nz))
  rw [hq,mul_assoc]
  congr 1
  exact (Rat.mul_den_eq_num t.1).symm

theorem signed_length_even (ws : CompilerWords.WordSum κ) : Even (signedWords ws).length := by
  unfold signedWords
  generalize denominator ws=D
  induction ws with
  | nil => exact ⟨0,rfl⟩
  | cons t ws ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_replicate]
    exact (show Even (2*((D:ℤ)*t.1.num/(t.1.den:ℤ)).natAbs) from ⟨((D:ℤ)*t.1.num/(t.1.den:ℤ)).natAbs,by omega⟩).add ih

theorem selectorCount_pos (ws : CompilerWords.WordSum κ) : 0 < selectorCount ws :=
  Nat.clog_pos (by omega) (by omega)

theorem packed_length (ws : CompilerWords.WordSum κ) : (packedWords ws).length=2^(selectorCount ws) := by
  have hb := Nat.le_pow_clog (by omega : 1 < 2) ((signedWords ws).length+2)
  change (signedWords ws).length+2 ≤ 2^(selectorCount ws) at hb
  obtain ⟨a,ha⟩ := signed_length_even ws
  have hpow : Even (2^(selectorCount ws)) := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (selectorCount_pos ws))
    rw [hk,pow_succ]
    exact ⟨2^k,by omega⟩
  obtain ⟨b,hb'⟩ := hpow
  simp only [packedWords,List.length_append,List.length_replicate]
  omega

theorem normalization_pos {ι : Type*} [Fintype ι] (P : Presentation ι) (r : Fin P.relations.length) :
    0 < normalization P r := by
  unfold normalization
  have hd : (0:ℚ) < denominator (relationWords P r) := by exact_mod_cast denominator_pos (relationWords P r)
  positivity

end
end E2.CompilerNetwork
