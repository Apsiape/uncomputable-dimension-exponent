import E2.CountEntropyScalar

namespace E2
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 600000

theorem binary_mass_entropy_superadd (a b c d : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    (a+b)*binaryEntropy (a/(a+b))+(c+d)*binaryEntropy (c/(c+d)) ≤
      (a+c+(b+d))*binaryEntropy ((a+c)/(a+c+(b+d))) := by
  by_cases hs : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0,hb0]
  by_cases ht : c+d=0
  · have hc0 : c=0 := by linarith
    have hd0 : d=0 := by linarith
    simp [hc0,hd0]
  have hs0 : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
  have ht0 : 0<c+d := lt_of_le_of_ne (add_nonneg hc hd) (Ne.symm ht)
  have hu : 0<a+b+(c+d) := add_pos hs0 ht0
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show a/(a+b) ∈ Set.Icc 0 1 from ⟨div_nonneg ha hs0.le,(div_le_one hs0).mpr (by linarith)⟩)
    (show c/(c+d) ∈ Set.Icc 0 1 from ⟨div_nonneg hc ht0.le,(div_le_one ht0).mpr (by linarith)⟩)
    (div_nonneg hs0.le hu.le) (div_nonneg ht0.le hu.le)
    (show (a+b)/(a+b+(c+d))+(c+d)/(a+b+(c+d))=1 by field_simp)
  have hm : (a+b)/(a+b+(c+d))*(a/(a+b))+
      (c+d)/(a+b+(c+d))*(c/(c+d))=(a+c)/(a+c+(b+d)) := by
    have hv : a+c+(b+d)≠0 := by linarith
    field_simp [hs,ht,ne_of_gt hu,hv]
    ring
  simp only [smul_eq_mul,hm] at h
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left h (div_nonneg hu.le hl.le)
  unfold binaryEntropy
  convert hscaled using 1 <;> field_simp [ne_of_gt hu] <;> ring

theorem binary_mass_entropy_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0≤a i) (hb : ∀ i, 0≤b i) :
    (∑ i∈s, (a i+b i)*binaryEntropy (a i/(a i+b i))) ≤
      ((∑ i∈s, a i)+(∑ i∈s, b i))*binaryEntropy ((∑ i∈s, a i)/((∑ i∈s, a i)+(∑ i∈s, b i))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hstep := binary_mass_entropy_superadd (a i) (b i) (∑ j∈s,a j) (∑ j∈s,b j) (ha i) (hb i)
      (Finset.sum_nonneg (fun j _ => ha j)) (Finset.sum_nonneg (fun j _ => hb j))
    linarith

theorem probability_entropy_two {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i∈s, 0≤w i) (hn : (∑ i∈s,w i)=1) (hc : s.card≤2) :
    (∑ i∈s, Real.negMulLog (w i)) ≤ Real.log 2 := by
  have hpoint (i : ι) (hi : i∈s) : 2*Real.negMulLog (w i) ≤
      1-2*w i+w i*(2*Real.log 2) := by
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg (by norm_num : (0:ℝ)≤2) (hw i hi))
    rw [Real.negMulLog_mul] at h
    simp only [Real.negMulLog] at h ⊢
    nlinarith
  have hs := Finset.sum_le_sum hpoint
  simp only [←Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one, ←Finset.sum_mul, hn] at hs
  have hcr : (s.card:ℝ)≤2 := by exact_mod_cast hc
  linarith

theorem mass_entropy_two {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0≤w i) (hc : s.card≤2) :
    (∑ i∈s, Real.negMulLog (w i))-Real.negMulLog (∑ i∈s,w i) ≤ (∑ i∈s,w i)*Real.log 2 := by
  let T := ∑ i∈s,w i
  have hT : 0≤T := Finset.sum_nonneg (fun i _ => hw i)
  by_cases hz : T=0
  · have hi : ∀ i∈s,w i=0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hz
    simp only [T] at hz
    simp only [hz, Real.negMulLog_zero, zero_mul, sub_zero]
    exact le_of_eq (Finset.sum_eq_zero (fun i hi' => by rw [hi i hi', Real.negMulLog_zero]))
  have hp := probability_entropy_two s (fun i => w i/T)
    (fun i _ => div_nonneg (hw i) hT)
    (by rw [← Finset.sum_div]; exact div_self hz) hc
  have he (i : ι) : Real.negMulLog (w i)=
      w i/T*Real.negMulLog T+T*Real.negMulLog (w i/T) := by
    rw [← Real.negMulLog_mul]
    congr 1
    exact (mul_div_cancel₀ (w i) hz).symm
  have hs : (∑ i∈s, Real.negMulLog (w i)) = Real.negMulLog T+T*(∑ i∈s, Real.negMulLog (w i/T)) := by
    simp_rw [he]
    rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.mul_sum, ←Finset.sum_div]
    change (T/T)*Real.negMulLog T+T*(∑ i∈s, Real.negMulLog (w i/T)) = _
    rw [div_self hz, one_mul]
  change _-Real.negMulLog T ≤ T*Real.log 2
  rw [hs]
  linarith [mul_le_mul_of_nonneg_left hp hT]

/-- Sharp ternary (and binary) classical Fano, in bits, at the actual error. -/
theorem classical_fano_three {n : ℕ} (hn : n≤3) (q : Fin n → Fin n → ℝ)
    (hq : ∀ a b, 0≤q a b) (hs : (∑ b, ∑ a,q a b)=1) :
    ((∑ b, ∑ a, Real.negMulLog (q a b))-(∑ b, Real.negMulLog (∑ a,q a b)))/Real.log 2 ≤
      binaryEntropy (∑ b, ∑ a∈Finset.univ.erase b,q a b)+(∑ b, ∑ a∈Finset.univ.erase b,q a b) := by
  classical
  let e : Fin n → ℝ := fun b => ∑ a∈Finset.univ.erase b,q a b
  let c : Fin n → ℝ := fun b => q b b
  have he : ∀ b,0≤e b := fun b => Finset.sum_nonneg (fun a _ => hq a b)
  have hc : ∀ b,0≤c b := fun b => hq b b
  have hcol (b : Fin n) : (∑ a,q a b)=e b+c b := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm
  have ht : (∑ b,e b)+(∑ b,c b)=1 := by
    rw [←Finset.sum_add_distrib]
    simpa only [←hcol] using hs
  have hbound (b : Fin n) :
      ((∑ a, Real.negMulLog (q a b))-Real.negMulLog (∑ a,q a b))/Real.log 2 ≤
        (e b+c b)*binaryEntropy (e b/(e b+c b))+e b := by
    have hw := mass_entropy_two (Finset.univ.erase b) (fun a => q a b) (fun a => hq a b)
      (by simp only [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin]; omega)
    have hb := binary_mass_entropy_log (e b) (c b) (he b) (hc b)
    have hsplit : (∑ a,Real.negMulLog (q a b))=
        (∑ a∈Finset.univ.erase b,Real.negMulLog (q a b))+Real.negMulLog (c b) := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm
    rw [hcol,hsplit]
    rw [hb]
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    have hlog : Real.log 2≠0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
    field_simp [hlog]
    change _-Real.negMulLog (e b)≤e b*Real.log 2 at hw
    linarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hbound b)
  have hbin := binary_mass_entropy_sum Finset.univ e c he hc
  rw [ht,div_one,one_mul] at hbin
  rw [Finset.sum_add_distrib, ←Finset.sum_div, Finset.sum_sub_distrib] at hsum
  change _≤binaryEntropy (∑ b,e b)+(∑ b,e b)
  linarith

theorem binary_entropy_mono_half {x y : ℝ} (hx : 0≤x) (hy : y≤1/2) (hxy : x≤y) :
    binaryEntropy x≤binaryEntropy y := by
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨hx,by linarith⟩ ⟨by linarith,by simpa only [one_div] using hy⟩ hxy

end
end E2
