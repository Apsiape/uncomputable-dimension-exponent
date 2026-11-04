import E2.SeparatedDigits
import E2.EffectiveApproximation

namespace E2.EffectiveNoncomputable
noncomputable section
open Encodable EffectiveCoding EffectiveApproximation

theorem theta_computable_of_beta (h : ComputableReal betaK) : ComputableReal thetaK := by
  obtain ⟨f,hf,herr⟩ := h
  have hshift : Computable (fun k : ℕ => k+2) :=
    Primrec.nat_add.to_comp.comp Computable.id (Computable.const 2)
  refine ⟨fun k => encode ((4:ℚ)*rationalCode (f (k+2)) + (-3)),
    Computable.encode.comp
      (rat_add.comp (rat_mul.comp (Computable.const 4)
        (rational_decode.to_comp.comp (hf.comp hshift))) (Computable.const (-3))), ?_⟩
  intro k
  rw [rational_encode]
  have he := herr (k+2)
  change |(rationalCode (f (k+2)) : ℝ)-betaK| ≤ radius (k+2) at he
  change |(↑((4:ℚ)*rationalCode (f (k+2))+(-3)):ℝ)-thetaK| ≤ radius k
  have heq : (↑((4:ℚ)*rationalCode (f (k+2))+(-3)):ℝ)-thetaK =
      4*((rationalCode (f (k+2)) : ℝ)-betaK) := by
    push_cast
    unfold betaK
    ring
  rw [heq,abs_mul]
  rw [abs_of_pos (by norm_num : (0:ℝ) < 4)]
  rw [radius_two] at he
  linarith

theorem beta_not_computable : ¬ ComputableReal betaK :=
  fun h => SeparatedDigits.theta_not_computable (theta_computable_of_beta h)

end
end E2.EffectiveNoncomputable
