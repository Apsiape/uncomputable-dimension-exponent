import E2.CantorRounding

namespace E2
noncomputable section

def cantorBranch (b : Bool) (x : ℝ) : ℝ := (if b then 3/4 else 0)+x/4

def prependBit (b : Bool) (tail : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | k+1 => tail k

theorem cantorCoordinate_prepend (b : Bool) (tail : ℕ → Bool) :
    cantorCoordinate (prependBit b tail)=cantorBranch b (cantorCoordinate tail) := by
  rw [cantorCoordinate_head]
  have ht : dropBits (prependBit b tail) 1=tail := by
    funext k
    simp only [dropBits,prependBit]
  rw [ht]
  cases b <;> simp [prependBit,cantorBranch] <;> ring

theorem cantorBranch_mem (b : Bool) {x : ℝ} (hx : x∈cantorSet) : cantorBranch b x∈cantorSet := by
  obtain ⟨tail,rfl⟩ := hx
  exact ⟨prependBit b tail,cantorCoordinate_prepend b tail⟩

theorem cantorBranch_dist (b : Bool) (x y : ℝ) :
    dist (cantorBranch b x) (cantorBranch b y)=dist x y/4 := by
  simp only [Real.dist_eq]
  have he : cantorBranch b x-cantorBranch b y=(x-y)/4 := by unfold cantorBranch; ring
  rw [he,abs_div]
  norm_num

theorem cantor_distance_unit {x : ℝ} (hx : 0≤x ∧ x≤1) : Metric.infDist x cantorSet≤1 := by
  have hzero : (0:ℝ)∈cantorSet := ⟨fun _ => false,cantorCoordinate_zero⟩
  have h := Metric.infDist_le_dist_of_mem (x:=x) hzero
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg hx.1] at h
  exact h.trans hx.2

/-- Cantor self-similarity of distance, including the comparison with the
opposite quarter. No continuity of a nearest-point choice is used. -/
theorem cantor_distance_branch (b : Bool) (x : ℝ) (hx : 0≤x ∧ x≤1) :
    Metric.infDist (cantorBranch b x) cantorSet=Metric.infDist x cantorSet/4 := by
  apply le_antisymm
  · obtain ⟨y,hy,he⟩ := cantor_nearest_exists x
    have h := Metric.infDist_le_dist_of_mem (x:=cantorBranch b x) (cantorBranch_mem b hy)
    rw [cantorBranch_dist,←he] at h
    exact h
  · apply (Metric.le_infDist cantorSet_nonempty).mpr
    rintro y ⟨c,rfl⟩
    have ht := cantorCoordinate_bounds (dropBits c 1)
    have hh := cantorCoordinate_head c
    have hdist := Metric.infDist_le_dist_of_mem (x:=x)
      (show cantorCoordinate (dropBits c 1)∈cantorSet from ⟨dropBits c 1,rfl⟩)
    by_cases hb : c 0=b
    · have he : cantorCoordinate c=cantorBranch b (cantorCoordinate (dropBits c 1)) := by
        rw [hh,hb]
        cases b <;> simp [cantorBranch] <;> ring
      rw [he,cantorBranch_dist]
      exact div_le_div_of_nonneg_right hdist (by norm_num)
    · have hu := cantor_distance_unit hx
      cases b with
      | false =>
        have hc : c 0=true := by cases h : c 0 <;> simp_all
        simp only [hc,↓reduceIte] at hh
        have he : cantorBranch false x=x/4 := by simp [cantorBranch]
        rw [he,Real.dist_eq,abs_of_nonpos (by linarith)]
        linarith
      | true =>
        have hc : c 0=false := by cases h : c 0 <;> simp_all
        simp only [hc,Bool.false_eq_true,↓reduceIte,zero_add] at hh
        have he : cantorBranch true x=3/4+x/4 := by simp [cantorBranch]
        rw [he,Real.dist_eq,abs_of_nonneg (by linarith)]
        linarith

theorem digitFunction_branch (b : Bool) (x : ℝ) (hx : 0≤x ∧ x≤1) :
    digitFunction (cantorBranch b x)=if b then 1 else 0 := by
  cases b with
  | false =>
    have hh : cantorBranch false x≤1/4 := by simp only [cantorBranch,Bool.false_eq_true,↓reduceIte,zero_add]; linarith
    simp only [digitFunction,hh,Bool.false_eq_true,↓reduceIte]
  | true =>
    have hh : ¬cantorBranch true x≤1/4 := by simp only [cantorBranch,↓reduceIte]; linarith
    simp only [digitFunction,hh,↓reduceIte]
    split <;> simp_all [cantorBranch] <;> linarith

end
end E2

#print axioms E2.cantorBranch
#print axioms E2.prependBit
#print axioms E2.cantorCoordinate_prepend
#print axioms E2.cantorBranch_mem
#print axioms E2.cantorBranch_dist
#print axioms E2.cantor_distance_unit
#print axioms E2.cantor_distance_branch
#print axioms E2.digitFunction_branch
