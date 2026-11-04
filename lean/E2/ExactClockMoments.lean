import E2.ExactTraceReal

namespace E2.ExactClock
noncomputable section
open scoped BigOperators Topology
variable {A : Type*} [CStarAlgebra A]

def digitProduct (l : List ℕ) (x : ℝ) : ℝ := (l.map (fun j => digitAt j x)).prod

theorem digitProduct_continuous (l : List ℕ) : Continuous (digitProduct l) :=
  continuous_list_prod l (fun j _ => (digitAt_lipschitz j).continuous)

theorem digitProduct_binary (l : List ℕ) (x : ℝ) (hx : x∈cantorSet) :
    digitProduct l x=0 ∨ digitProduct l x=1 := by
  obtain ⟨bits,rfl⟩ := hx
  induction l with
  | nil => simp [digitProduct]
  | cons j l ih =>
    change digitAt j (cantorCoordinate bits)*digitProduct l (cantorCoordinate bits)=0 ∨
      digitAt j (cantorCoordinate bits)*digitProduct l (cantorCoordinate bits)=1
    rw [digitAt_on_bits]
    cases h : bits j with
    | false => simp
    | true => simpa only [ite_true,one_mul] using ih

theorem digitProduct_one (l : List ℕ) : digitProduct l 1=1 := by
  calc
    digitProduct l 1=digitProduct l (cantorCoordinate (fun _ => true)) :=
      congrArg (digitProduct l) cantorCoordinate_one.symm
    _=1 := by simp [digitProduct,digitAt_on_bits]

theorem digitProduct_cfc (a : A) (ha : IsSelfAdjoint a) (l : List ℕ) :
    cfc (digitProduct l) a=(l.map (fun j => cfc (digitAt j) a)).prod := by
  induction l with
  | nil => exact cfc_const_one ℝ a ha
  | cons j l ih =>
    have he : digitProduct (j::l)=(fun x => digitAt j x*digitProduct l x) := rfl
    rw [he,cfc_mul _ _ a (digitAt_lipschitz j).continuous.continuousOn
      (digitProduct_continuous l).continuousOn,ih]
    rfl

/-- The zero set of a continuous finite cylinder is uniformly separated from one. -/
theorem top_gap (s : Set ℝ) (hs : IsCompact s) (hb : s ⊆ Set.Icc 0 1)
    (hK : s ⊆ cantorSet) (l : List ℕ) :
    ∃ r : ℝ, 0≤r ∧ r<1 ∧ ∀ x∈s, digitProduct l x=0 → x≤r := by
  let E := s ∩ (digitProduct l) ⁻¹' {0}
  have hE : IsCompact E := hs.inter_right ((isClosed_singleton).preimage (digitProduct_continuous l))
  by_cases he : E.Nonempty
  · obtain ⟨r,hr,hmax⟩ := hE.exists_isGreatest he
    refine ⟨r,(hb hr.1).1,?_,fun x hx hq => hmax ⟨hx,hq⟩⟩
    apply lt_of_le_of_ne (hb hr.1).2
    intro heq
    have h0 : digitProduct l r=0 := hr.2
    rw [heq,digitProduct_one] at h0
    norm_num at h0
  · refine ⟨0,le_rfl,by norm_num,?_⟩
    intro x hx hq
    exact False.elim (he ⟨x,hx,hq⟩)

/-- A finite top cylinder bounds every moment by its mass plus a decaying power. -/
theorem moment_bound (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (hσ : spectrum ℝ a ⊆ Set.Icc 0 1) (hK : spectrum ℝ a ⊆ cantorSet) (l : List ℕ) :
    ∃ r : ℝ, 0≤r ∧ r<1 ∧ ∀ n : ℕ,
      (τ.toLinearMap (a^n)).re≤(τ.toLinearMap (cfc (digitProduct l) a)).re+r^n := by
  obtain ⟨r,hr0,hr1,hgap⟩ := top_gap (spectrum ℝ a) (spectrum.isCompact a) hσ hK l
  refine ⟨r,hr0,hr1,?_⟩
  intro n
  have hb : ∀ x∈spectrum ℝ a, x^n≤digitProduct l x+r^n := by
    intro x hx
    rcases digitProduct_binary l x (hK hx) with hq | hq
    · rw [hq,zero_add]
      exact pow_le_pow_left₀ (hσ hx).1 (hgap x hx hq) n
    · rw [hq]
      have h := pow_le_one₀ (hσ hx).1 (hσ hx).2 (n:=n)
      linarith [pow_nonneg hr0 n]
  have h := ExactTrace.cfc_mono τ a ha (fun x : ℝ => x^n)
    (fun x => digitProduct l x+r^n) (by fun_prop)
    ((digitProduct_continuous l).add continuous_const).continuousOn hb
  rw [cfc_pow_id (R:=ℝ) a n ha,cfc_add a _ _ (digitProduct_continuous l).continuousOn continuousOn_const,
    map_add,Complex.add_re,ExactTrace.cfc_const τ a ha] at h
  exact h

/-- All-ones cylinder masses tending to zero imply vanishing real moments. -/
theorem moments_zero (τ : TracialState A) (a : A) (ha : IsSelfAdjoint a)
    (hσ : spectrum ℝ a ⊆ Set.Icc 0 1) (hK : spectrum ℝ a ⊆ cantorSet)
    (hmass : ∀ M : ℕ, (τ.toLinearMap
      (cfc (digitProduct ((List.finRange M).map Fin.val)) a)).re=(1/2:ℝ)^M) :
    Filter.Tendsto (fun n : ℕ => (τ.toLinearMap (a^n)).re) Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hhalf : (0:ℝ)<ε/2 := by linarith
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)
  obtain ⟨M,hM⟩ := (hg.eventually (gt_mem_nhds hhalf)).exists
  obtain ⟨r,hr0,hr1,hbound⟩ := moment_bound τ a ha hσ hK ((List.finRange M).map Fin.val)
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (hr.eventually (gt_mem_nhds hhalf))
  refine ⟨N,fun n hn => ?_⟩
  have hnonneg : 0≤(τ.toLinearMap (a^n)).re := by
    rw [←cfc_pow_id (R:=ℝ) a n ha]
    exact ExactTrace.cfc_nonneg τ a ha (fun x : ℝ => x^n) (by fun_prop)
      (fun x hx => pow_nonneg (hσ hx).1 n)
  have hb := hbound n
  rw [hmass M] at hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  linarith [hN n hn]

end
end E2.ExactClock

