import E2.Clock
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace E2.ExactClock
noncomputable section
open scoped Topology
variable {A : Type*} [CStarAlgebra A]

/-- Continuous real functional calculus respects an arbitrary intertwiner. -/
theorem intertwines (a b z : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hz : a*z=z*b) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f a*z=z*cfc f b := by
  let s := spectrum ℝ a ∪ spectrum ℝ b
  have hs : IsCompact s := (spectrum.isCompact a).union (spectrum.isCompact b)
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let φ := cfcHomSuperset ha (show spectrum ℝ a ⊆ s from Set.subset_union_left)
  let ψ := cfcHomSuperset hb (show spectrum ℝ b ⊆ s from Set.subset_union_right)
  have h (g : C(s, ℝ)) : φ g*z=z*ψ g := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change φ (algebraMap ℝ C(s, ℝ) r)*z=z*ψ (algebraMap ℝ C(s, ℝ) r)
      rw [AlgHomClass.commutes, AlgHomClass.commutes]
      exact Algebra.commutes r z
    | id => simpa only [φ,ψ,cfcHomSuperset_id] using hz
    | star_id => simpa only [star_trivial,φ,ψ,cfcHomSuperset_id] using hz
    | add g h hg hh => simpa only [map_add,add_mul,mul_add,hg,hh]
    | mul g h hg hh =>
      simp only [map_mul]
      calc
        _ = φ g*(φ h*z) := mul_assoc _ _ _
        _ = φ g*(z*ψ h) := by rw [hh]
        _ = (φ g*z)*ψ h := (mul_assoc _ _ _).symm
        _ = _ := by rw [hg,mul_assoc]
    | frequently g hg =>
      have hc : IsClosed {g : C(s, ℝ) | φ g*z=z*ψ g} :=
        isClosed_eq ((cfcHomSuperset_continuous ha _).mul_const z)
          ((cfcHomSuperset_continuous hb _).const_mul z)
      exact hc.mem_of_frequently_of_tendsto hg Filter.tendsto_id
  rw [cfc_apply f a ha hf.continuousOn,cfc_apply f b hb hf.continuousOn]
  exact h ⟨fun x => f x, hf.comp continuous_subtype_val⟩

 theorem conjugate (u a : A) (hu : star u*u=1 ∧ u*star u=1)
    (ha : IsSelfAdjoint a) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (u*a*star u)=u*cfc f a*star u := by
  have hb : IsSelfAdjoint (u*a*star u) := by
    change star (u*a*star u)=u*a*star u
    simp only [star_mul,star_star,ha.star_eq,mul_assoc]
  have hz : (u*a*star u)*u=u*a := by rw [mul_assoc,mul_assoc,hu.1,mul_one]
  have h := intertwines (u*a*star u) a u hb ha hz f hf
  have h' := congrArg (fun w : A => w*star u) h
  simpa only [mul_assoc,hu.2,mul_one] using h'

end
end E2.ExactClock

