import E2.HaltingApproximation
import E2.HaltingReduction

namespace E2.HaltingDegree
noncomputable section
set_option maxHeartbeats 300000
open Encodable EffectiveCoding EffectiveOracle HaltingReduction HaltingApproximation
attribute [local instance] Classical.propDecidable
open Nat.Partrec (Code)
open Nat.Partrec.Code

 theorem re_reducible (p : ℕ → Prop) (hp : REPred p) :
    TuringReducible (fun n => Part.some (if p n then 1 else 0)) haltingOracle := by
  have hf : Partrec (fun n => Part.assert (p n) (fun _ => Part.some (0:ℕ))) := by
    refine (hp.map (Computable.const (0:ℕ)).to₂).of_eq ?_
    intro n
    apply Part.ext
    intro v
    simp [eq_comm]
  obtain ⟨c,hc⟩ := exists_code.mp (Partrec.nat_iff.mp hf)
  let q : ℕ → ℕ := fun n => encode (Code.comp c (Code.const n))
  have hq : Computable q := Computable.encode.comp
    (primrec₂_comp.to_comp.comp (Computable.const c) primrec_const.to_comp)
  have he (n : ℕ) : (q n ∈ E2.haltingSet) ↔ p n := by
    simp only [q,E2.haltingSet,Set.mem_setOf_eq,←ofNatCode_eq,Denumerable.ofNat_encode]
    rw [Code.eval]
    simp only [eval_const,Part.bind_some,hc]
    simp [Part.assert]
  have ho : Nat.RecursiveIn {haltingOracle} haltingOracle := .oracle _ (by simp)
  have hr := ho.comp (total_computable (O := {haltingOracle}) hq)
  apply RecursiveIn.iff_nat.mpr
  refine hr.of_eq ?_
  intro n
  exact (Part.bind_some (q n) (fun m => haltingOracle m)).trans
    (by simp only [haltingOracle,he])

 theorem lower_cut_re : REPred (fun n => (rationalCode n : ℝ) < thetaK) := by
  let P : ℕ → ℕ → Prop := fun n s => rationalCode n < stage s
  have hp : ComputablePred (fun p : ℕ × ℕ => P p.1 p.2) :=
    (rat_lt.decide.to_comp.comp (rational_decode.to_comp.comp Computable.fst)
      (stage_computable.comp Computable.snd)).computablePred
  have hfind : Partrec (fun n => Nat.rfind (fun s => Part.some (decide (P n s)))) :=
    Partrec.rfind hp.decide.partrec
  have hdom (n : ℕ) : (Nat.rfind (fun s => Part.some (decide (P n s)))).Dom ↔
      (rationalCode n : ℝ) < thetaK := by
    have hr := Nat.rfind_dom (p := fun s => Part.some (decide (P n s)))
    constructor
    · intro hh
      obtain ⟨s,hs,-⟩ := hr.mp hh
      have hps : P n s := by simpa using hs
      have hc : (rationalCode n : ℝ) < (stage s : ℝ) := Rat.cast_lt.mpr hps
      exact hc.trans_le (stage_le s)
    · intro hn
      apply hr.mpr
      have hev : ∀ᶠ s in Filter.atTop, (rationalCode n : ℝ) < (stage s : ℝ) :=
        stage_limit.eventually (lt_mem_nhds hn)
      obtain ⟨s,hs⟩ := hev.exists
      exact ⟨s,by simpa [P] using (Rat.cast_lt.mp hs),fun {_} _ => trivial⟩
  exact hfind.dom_re.of_eq hdom

 theorem theta_reducible_to_halting : TuringReducible (realOracle thetaK) haltingOracle :=
  re_reducible _ lower_cut_re

 theorem theta_equivalent : TuringEquivalent (realOracle thetaK) haltingOracle :=
  ⟨theta_reducible_to_halting,halting_reducible_to_theta⟩

end
end E2.HaltingDegree
