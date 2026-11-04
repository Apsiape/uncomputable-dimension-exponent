import E2.MomentCentralizer

namespace E2.ExactCompactness
noncomputable section
open Filter
open scoped ENNReal
variable {I : Type*} {B : I → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]

variable (φ : ∀ i, B i →ₗ[ℂ] ℂ) (K : ℝ) (hK : 0≤K) (hbound : ∀ i x, ‖φ i x‖≤K*‖x‖)

def limitValue (u : Ultrafilter I) (a : BoundedProduct B) : ℂ :=
  limUnder (u:Filter I) (fun i => φ i (a i))

include K hK hbound

theorem limitValue_tendsto (u : Ultrafilter I) (a : BoundedProduct B) :
    Tendsto (fun i => φ i (a i)) (u:Filter I) (nhds (limitValue φ u a)) := by
  apply tendsto_nhds_limUnder
  let f := fun i => φ i (a i)
  have hmem : Metric.closedBall (0:ℂ) (K*‖a‖) ∈ u.map f := by
    change {i | f i ∈ Metric.closedBall (0:ℂ) (K*‖a‖)} ∈ (u:Filter I)
    apply Filter.Eventually.of_forall
    intro i
    simp only [Metric.mem_closedBall,dist_zero_right,f]
    exact (hbound i (a i)).trans (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero a i) hK)
  obtain ⟨z,hz,hlim⟩ := (isCompact_closedBall (0:ℂ) (K*‖a‖)).ultrafilter_le_nhds' (u.map f) hmem
  exact ⟨z,hlim⟩

def limitLinear (u : Ultrafilter I) : BoundedProduct B →ₗ[ℂ] ℂ where
  toFun := limitValue φ u
  map_add' a b := by
    have h := (limitValue_tendsto φ K hK hbound u a).add (limitValue_tendsto φ K hK hbound u b)
    have hh : Tendsto (fun i => φ i ((a+b) i)) (u:Filter I)
        (nhds (limitValue φ u a+limitValue φ u b)) := by
      simpa only [lp.coeFn_add,Pi.add_apply,map_add] using h
    exact tendsto_nhds_unique (limitValue_tendsto φ K hK hbound u (a+b)) hh
  map_smul' c a := by
    have h := (limitValue_tendsto φ K hK hbound u a).const_smul c
    have hh : Tendsto (fun i => φ i ((c • a) i)) (u:Filter I)
        (nhds (c • limitValue φ u a)) := by
      simpa only [lp.coeFn_smul,Pi.smul_apply,map_smul,RingHom.id_apply] using h
    exact tendsto_nhds_unique (limitValue_tendsto φ K hK hbound u (c • a)) hh

theorem limitValue_bound (u : Ultrafilter I) (a : BoundedProduct B) :
    ‖limitValue φ u a‖≤K*‖a‖ := by
  apply le_of_tendsto (limitValue_tendsto φ K hK hbound u a).norm
  apply Filter.Eventually.of_forall
  intro i
  exact (hbound i (a i)).trans (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero a i) hK)

def limitFunctional (u : Ultrafilter I) : BoundedProduct B →L[ℂ] ℂ :=
  (limitLinear φ K hK hbound u).mkContinuous K (limitValue_bound φ K hK hbound u)

theorem limitFunctional_star (hstar : ∀ i x, φ i (star x)=star (φ i x))
    (u : Ultrafilter I) (a : BoundedProduct B) :
    limitFunctional φ K hK hbound u (star a)=star (limitFunctional φ K hK hbound u a) := by
  have h := (limitValue_tendsto φ K hK hbound u a).star
  have hh : Tendsto (fun i => φ i ((star a) i)) (u:Filter I)
      (nhds (star (limitValue φ u a))) := by
    simpa only [lp.coeFn_star,Pi.star_apply,hstar] using h
  exact tendsto_nhds_unique (limitValue_tendsto φ K hK hbound u (star a)) hh

theorem limitFunctional_positive (hpos : ∀ i x, 0≤(φ i (star x*x)).re)
    (u : Ultrafilter I) (a : BoundedProduct B) :
    0≤(limitFunctional φ K hK hbound u (star a*a)).re := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (Complex.continuous_re.tendsto _ |>.comp (limitValue_tendsto φ K hK hbound u (star a*a)))
  exact Filter.Eventually.of_forall (fun i => hpos i (a i))

theorem limitFunctional_one (h1 : ∀ i, φ i 1=1) (u : Ultrafilter I) :
    limitFunctional φ K hK hbound u 1=1 := by
  have h := limitValue_tendsto φ K hK hbound u 1
  have hh : Tendsto (fun i => φ i ((1:BoundedProduct B) i)) (u:Filter I) (nhds (1:ℂ)) := by
    simpa only [lp.infty_coeFn_one,Pi.one_apply,h1] using (tendsto_const_nhds : Tendsto (fun _ : I => (1:ℂ)) (u:Filter I) (nhds 1))
  exact tendsto_nhds_unique h hh

end
end E2.ExactCompactness
