import E2.CantorBits

namespace E2
noncomputable section
open scoped BigOperators

theorem cantorWeight_le_one (j : ℕ) : cantorWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)≤1)

theorem carryOnBits_bounds (b : ℕ → Bool) : 0 ≤ carryOnBits b ∧ carryOnBits b ≤ 1 := by
  unfold carryOnBits
  split
  · rw [← cantorWeight_zpow]
    exact ⟨cantorWeight_nonneg _,cantorWeight_le_one _⟩
  · norm_num

theorem carryOnBits_first_zero (b : ℕ → Bool) (k : ℕ)
    (hpre : ∀ j<k, b j=true) (hk : b k=false) : carryOnBits b=cantorWeight k := by
  classical
  have hex : ∃ j,b j=false := ⟨k,hk⟩
  have hfind : Nat.find hex=k := (Nat.find_eq_iff hex).mpr
    ⟨hk,fun j hj => by rw [hpre j hj]; decide⟩
  rw [carryOnBits,dif_pos hex,hfind,← cantorWeight_zpow]

theorem carryOnBits_all_ones (b : ℕ → Bool) (h : ∀ j,b j=true) : carryOnBits b=0 := by
  unfold carryOnBits
  rw [dif_neg (by rintro ⟨j,hj⟩; simpa [h j] using hj)]

theorem carryOnBits_head (b : ℕ → Bool) :
    carryOnBits b = if b 0 then (1/4)*carryOnBits (dropBits b 1) else 1 := by
  classical
  cases hb : b 0
  · rw [if_neg (by simp [hb]),carryOnBits_first_zero b 0 (by simp) hb]
    rfl
  · rw [if_pos (by simp [hb])]
    by_cases ht : ∃ k,dropBits b 1 k=false
    · let k := Nat.find ht
      have hpre : ∀ j<k,dropBits b 1 j=true := by
        intro j hj
        have hn := Nat.find_min ht hj
        cases he : dropBits b 1 j <;> simp_all
      have hk := Nat.find_spec ht
      have hpre' : ∀ j<k+1,b j=true := by
        intro j hj
        cases j with
        | zero => exact hb
        | succ j => exact hpre j (by omega)
      rw [carryOnBits_first_zero b (k+1) hpre' hk,
        carryOnBits_first_zero (dropBits b 1) k hpre hk,cantorWeight_succ]
    · have htail : ∀ j,dropBits b 1 j=true := by
        intro j
        have hn := not_exists.mp ht j
        cases he : dropBits b 1 j <;> simp_all
      have hall : ∀ j,b j=true := by
        intro j
        cases j with
        | zero => exact hb
        | succ j => exact htail j
      rw [carryOnBits_all_ones b hall,carryOnBits_all_ones _ htail,mul_zero]

theorem carryOnBits_prefix_bound (b c : ℕ → Bool) (j : ℕ)
    (h : ∀ k<j,b k=c k) : |carryOnBits b-carryOnBits c| ≤ cantorWeight j := by
  induction j generalizing b c with
  | zero =>
    have hb := carryOnBits_bounds b
    have hc := carryOnBits_bounds c
    rw [show cantorWeight 0=1 from rfl,abs_le]
    constructor <;> linarith
  | succ j ih =>
    have h0 := h 0 (by omega)
    have ht : ∀ k<j,dropBits b 1 k=dropBits c 1 k := fun k hk => h (k+1) (by omega)
    rw [carryOnBits_head b,carryOnBits_head c,h0,cantorWeight_succ]
    cases hc0 : c 0
    · simp only [hc0,Bool.false_eq_true,reduceIte,sub_self,abs_zero]
      exact mul_nonneg (by norm_num) (cantorWeight_nonneg _)
    · simp only [hc0,Bool.true_eq,reduceIte]
      rw [← mul_sub,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/4)]
      exact mul_le_mul_of_nonneg_left (ih _ _ ht) (by norm_num)

/-- The factor two comes from the separated base-four cylinders. -/
theorem prefix_bound_implies_cantor_lipschitz (f : (ℕ → Bool) → ℝ)
    (hf : ∀ b c j, (∀ k<j,b k=c k) → |f b-f c| ≤ cantorWeight j) :
    ∀ b c, |f b-f c| ≤ 2*|cantorCoordinate b-cantorCoordinate c| := by
  classical
  intro b c
  by_cases hbc : b=c
  · simp [hbc]
  have hex : ∃ j,b j≠c j := by
    by_contra h
    apply hbc
    funext j
    simpa using not_exists.mp h j
  let j := Nat.find hex
  have hpre : ∀ k<j,b k=c k := fun k hk => by simpa using Nat.find_min hex hk
  have hlo := cantorCoordinate_first_difference b c j hpre (Nat.find_spec hex)
  have hhi := hf b c j hpre
  linarith

theorem addBits_coordinate_lipschitz (i : ℕ) (b c : ℕ → Bool) :
    |cantorCoordinate (addBits i b)-cantorCoordinate (addBits i c)| ≤
      2*|cantorCoordinate b-cantorCoordinate c| := by
  apply prefix_bound_implies_cantor_lipschitz (fun b => cantorCoordinate (addBits i b)) _ b c
  intro b c j h
  exact cantorCoordinate_prefix_bound _ _ j (addBits_prefix_agree i b c j h)

theorem carryOnBits_lipschitz (b c : ℕ → Bool) :
    |carryOnBits b-carryOnBits c| ≤ 2*|cantorCoordinate b-cantorCoordinate c| :=
  prefix_bound_implies_cantor_lipschitz carryOnBits carryOnBits_prefix_bound b c

def cantorExtension (f : (ℕ → Bool) → ℝ) (x : ℝ) : ℝ :=
  sInf (Set.range (fun b => f b+2*|x-cantorCoordinate b|))

theorem cantorExtension_bdd (f : (ℕ → Bool) → ℝ) (hf : ∀ b,0≤f b) (x : ℝ) :
    BddBelow (Set.range (fun b => f b+2*|x-cantorCoordinate b|)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨b,rfl⟩
  exact add_nonneg (hf b) (mul_nonneg (by norm_num) (abs_nonneg _))

theorem cantorExtension_le (f : (ℕ → Bool) → ℝ) (hf : ∀ b,0≤f b) (x : ℝ) (b : ℕ → Bool) :
    cantorExtension f x ≤ f b+2*|x-cantorCoordinate b| :=
  csInf_le (cantorExtension_bdd f hf x) ⟨b,rfl⟩

/-- Direct proof for the exact sInf formula in the blueprint. -/
theorem cantorExtension_lipschitz (f : (ℕ → Bool) → ℝ) (hf : ∀ b,0≤f b) :
    LipschitzWith 2 (cantorExtension f) := by
  apply LipschitzWith.of_le_add_mul 2
  intro x y
  rw [← sub_le_iff_le_add]
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨b,rfl⟩
  rw [sub_le_iff_le_add]
  have h := cantorExtension_le f hf x b
  have ht := abs_sub_le x y (cantorCoordinate b)
  rw [Real.dist_eq]
  norm_num at *
  linarith

theorem cantorExtension_eq (f : (ℕ → Bool) → ℝ) (hf : ∀ b,0≤f b)
    (hlip : ∀ b c,|f b-f c| ≤ 2*|cantorCoordinate b-cantorCoordinate c|) (b : ℕ → Bool) :
    cantorExtension f (cantorCoordinate b)=f b := by
  apply le_antisymm
  · simpa using cantorExtension_le f hf (cantorCoordinate b) b
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨c,rfl⟩
    have h := (le_abs_self (f b-f c)).trans (hlip b c)
    linarith

theorem cantorTranslation_lipschitz (i : ℕ) : LipschitzWith 2 (cantorTranslation i) :=
  cantorExtension_lipschitz _ (fun b => (cantorCoordinate_bounds _).1)
theorem carryFunction_lipschitz : LipschitzWith 2 carryFunction :=
  cantorExtension_lipschitz _ (fun b => (carryOnBits_bounds _).1)
theorem cantorTranslation_on_bits (i : ℕ) (b : ℕ → Bool) :
    cantorTranslation i (cantorCoordinate b)=cantorCoordinate (addBits i b) :=
  cantorExtension_eq _ (fun b => (cantorCoordinate_bounds _).1) (addBits_coordinate_lipschitz i) b
theorem carryFunction_on_bits (b : ℕ → Bool) :
    carryFunction (cantorCoordinate b)=carryOnBits b :=
  cantorExtension_eq _ (fun b => (carryOnBits_bounds _).1) carryOnBits_lipschitz b

theorem digitFunction_on_bits (b : ℕ → Bool) :
    digitFunction (cantorCoordinate b)=if b 0 then 1 else 0 := by
  have hhead := cantorCoordinate_head b
  have ht := cantorCoordinate_bounds (dropBits b 1)
  cases hb : b 0
  · simp only [hb,Bool.false_eq_true,reduceIte] at *
    have hlow : cantorCoordinate b≤1/4 := by linarith
    unfold digitFunction
    rw [ite_eq_left hlow]
  · simp only [hb,Bool.true_eq,reduceIte] at *
    have hhi : 3/4≤cantorCoordinate b := by linarith
    have hnot : ¬cantorCoordinate b≤1/4 := by linarith
    unfold digitFunction
    rw [ite_eq_right hnot]
    by_cases hle : cantorCoordinate b≤3/4
    · rw [ite_eq_left hle]
      linarith
    · rw [ite_eq_right hle]

theorem tailFunction_on_bits (b : ℕ → Bool) :
    tailFunction (cantorCoordinate b)=cantorCoordinate (dropBits b 1) := by
  rw [tailFunction,digitFunction_on_bits]
  have h := cantorCoordinate_head b
  cases hb : b 0 <;> simp only [hb,Bool.false_eq_true,Bool.true_eq,reduceIte] at * <;> linarith

theorem carryFunction_recursion (a : ℝ) (ha : a∈cantorSet) :
    carryFunction a=1-digitFunction a+(1/4)*digitFunction a*carryFunction (tailFunction a) := by
  obtain ⟨b,rfl⟩ := ha
  rw [carryFunction_on_bits,digitFunction_on_bits,tailFunction_on_bits,carryFunction_on_bits]
  rw [carryOnBits_head]
  cases b 0 <;> norm_num

theorem cantorTranslation_composition (i j : ℕ) (a : ℝ) (ha : a∈cantorSet) :
    cantorTranslation (i+j) a=cantorTranslation i (cantorTranslation j a) := by
  obtain ⟨b,rfl⟩ := ha
  rw [cantorTranslation_on_bits,cantorTranslation_on_bits,cantorTranslation_on_bits,addBits_comp]

theorem binaryPrefix_ones (M : ℕ) : binaryPrefix (fun _ => true) M+1=2^M := by
  induction M with
  | zero => simp [binaryPrefix]
  | succ M ih =>
    rw [binaryPrefix_succ,pow_succ]
    simp only [Bool.true_eq,reduceIte]
    omega

theorem addBits_one_all_ones : addBits 1 (fun _ => true)=(fun _ => false) := by
  funext j
  rw [addBits_eq]
  have he : 1+binaryPrefix (fun _ => true) (j+1)=2^(j+1) := by
    have := binaryPrefix_ones (j+1)
    omega
  rw [he,pow_succ,Nat.mul_comm (2^j) 2,Nat.mul_div_left _ (by positivity : 0<2^j)]
  decide

theorem cantorCoordinate_increment_first_zero (k : ℕ) (b : ℕ → Bool)
    (hpre : ∀ j<k,b j=true) (hk : b k=false) :
    cantorCoordinate (addBits 1 b)=cantorCoordinate b-1+(7/4)*carryOnBits b := by
  induction k generalizing b with
  | zero =>
    have h := cantorCoordinate_head b
    have ho := cantorCoordinate_head (addBits 1 b)
    have hc := carryOnBits_head b
    rw [addBits_one_head,addBits_one_tail] at ho
    simp only [hk,Bool.not_false,Bool.false_eq_true,Bool.true_eq,reduceIte,addBits_zero] at h ho hc
    linarith
  | succ k ih =>
    have hb : b 0=true := hpre 0 (by omega)
    have htpre : ∀ j<k,dropBits b 1 j=true := fun j hj => hpre (j+1) (by omega)
    have htk : dropBits b 1 k=false := hk
    have hi := ih (dropBits b 1) htpre htk
    have h := cantorCoordinate_head b
    have ho := cantorCoordinate_head (addBits 1 b)
    have hc := carryOnBits_head b
    rw [addBits_one_head,addBits_one_tail] at ho
    simp only [hb,Bool.not_true,Bool.false_eq_true,Bool.true_eq,reduceIte] at h ho hc
    linarith

theorem cantorCoordinate_increment (b : ℕ → Bool) :
    cantorCoordinate (addBits 1 b)=cantorCoordinate b-1+(7/4)*carryOnBits b := by
  classical
  by_cases h : ∃ k,b k=false
  · apply cantorCoordinate_increment_first_zero (Nat.find h) b _ (Nat.find_spec h)
    intro j hj
    have hn := Nat.find_min h hj
    cases he : b j <;> simp_all
  · have hb : b=(fun _ => true) := by
      funext j
      have hn := not_exists.mp h j
      cases he : b j <;> simp_all
    rw [hb,addBits_one_all_ones,cantorCoordinate_zero,cantorCoordinate_one,
      carryOnBits_all_ones _ (fun _ => rfl)]
    norm_num

theorem cantorTranslation_one (a : ℝ) (ha : a∈cantorSet) :
    cantorTranslation 1 a=a-1+(7/4)*carryFunction a := by
  obtain ⟨b,rfl⟩ := ha
  rw [cantorTranslation_on_bits,carryFunction_on_bits]
  exact cantorCoordinate_increment b

end
end E2
