import E2.EffectiveCoding

namespace E2.EffectiveApproximation
noncomputable section
open Filter EffectiveCoding

def radius (k : ℕ) : ℝ := (2:ℝ)^(-(k+1:ℤ))

theorem radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

theorem radius_succ (k : ℕ) : radius (k+1) = radius k / 2 := by
  unfold radius
  rw [show -(↑(k+1)+1:ℤ) = -(k+1:ℤ) + (-1) by push_cast; ring,
    zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  norm_num
  ring

theorem radius_two (k : ℕ) : radius (k+2) = radius k / 4 := by
  rw [show k+2 = (k+1)+1 by omega, radius_succ, radius_succ]
  ring

theorem certified_limit (a : ℕ → ℝ) (β : ℝ)
    (ha : ComputableRealSequence a) (hr : CertifiedRate a β) : ComputableReal β := by
  obtain ⟨f,hf,he⟩ := ha
  obtain ⟨r,⟨g,hg,hgerr⟩,hrlim,hbound⟩ := hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound
  let P : ℕ → ℕ → Prop := fun k n => N ≤ n ∧
    rationalCode (g (n,k+2)) < (2:ℚ)^(-(↑(k+1)+1:ℤ))
  have hp : ComputablePred (fun p : ℕ × ℕ => P p.1 p.2) := by
    have hkn : Computable (fun p : ℕ × ℕ => (p.2,p.1+2)) :=
      Computable.snd.pair (Primrec.nat_add.to_comp.comp Computable.fst (Computable.const 2))
    have hgq : Computable (fun p : ℕ × ℕ => rationalCode (g (p.2,p.1+2))) := rational_decode.to_comp.comp (hg.comp hkn)
    have hq : Computable (fun p : ℕ × ℕ => (2:ℚ)^(-(↑(p.1+1)+1:ℤ))) := rat_pow_two.comp (Computable.succ.comp Computable.fst)
    apply Computable.computablePred
    exact (Primrec.and.to_comp.comp
      (Primrec.nat_le.decide.to_comp.comp (Computable.const N) Computable.snd)
      (rat_lt.decide.to_comp.comp hgq hq)).of_eq (fun p => by simp [P])
  have hex : ∀ k, ∃ n, P k n := by
    intro k
    have hev : ∀ᶠ n in atTop, r n < radius k / 4 :=
      hrlim.eventually (gt_mem_nhds (by have := radius_pos k; linarith))
    obtain ⟨n,hn,hsmall⟩ := ((eventually_ge_atTop N).and hev).exists
    refine ⟨n,hn,?_⟩
    have hg0 := (abs_le.mp (hgerr n (k+2))).2
    change (rationalCode (g (n,k+2)) : ℝ) - r n ≤ radius (k+2) at hg0
    have hcast : (↑((2:ℚ)^(-(↑(k+1)+1:ℤ))) : ℝ) = radius (k+1) := by
      simp [radius]
    apply (Rat.cast_lt (K := ℝ)).mp
    rw [hcast, radius_succ]
    rw [radius_two] at hg0
    linarith
  let s : ℕ → ℕ := fun k => Nat.find (hex k)
  have hs : Computable s := Computable.find hp hex
  refine ⟨fun k => f (s k,k+2),
    hf.comp (hs.pair (Primrec.nat_add.to_comp.comp Computable.id (Computable.const 2))), ?_⟩
  intro k
  have hsel := Nat.find_spec (hex k)
  have hsmall : (rationalCode (g (s k,k+2)) : ℝ) < radius k / 2 := by
    have h : (rationalCode (g (s k,k+2)) : ℝ) <
        (↑((2:ℚ)^(-(↑(k+1)+1:ℤ))) : ℝ) := Rat.cast_lt.mpr hsel.2
    rw [Rat.cast_zpow] at h
    norm_num only [Rat.cast_ofNat] at h
    change _ < radius (k+1) at h
    rwa [radius_succ] at h
  have hg0 := (abs_le.mp (hgerr (s k) (k+2))).1
  have ha0 := he (s k) (k+2)
  change -radius (k+2) ≤ (rationalCode (g (s k,k+2)) : ℝ) - r (s k) at hg0
  change |(rationalCode (f (s k,k+2)) : ℝ) - a (s k)| ≤ radius (k+2) at ha0
  change |(rationalCode (f (s k,k+2)) : ℝ) - β| ≤ radius k
  have hbound0 := hN (s k) hsel.1
  calc
    _ ≤ |(rationalCode (f (s k,k+2)) : ℝ) - a (s k)| + |a (s k)-β| :=
      abs_sub_le _ _ _
    _ ≤ radius (k+2) + r (s k) := add_le_add ha0 hbound0
    _ ≤ radius k := by rw [radius_two] at hg0 ⊢; linarith

end
end E2.EffectiveApproximation
