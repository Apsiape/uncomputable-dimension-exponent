import E2.ExactClockBase

namespace E2.ExactClock
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem real_smul (r : ℝ) (a : A) : r • a=(r:ℂ) • a := by
  exact (IsScalarTower.algebraMap_smul ℂ r a).symm

def branch (b : A) (bit : Bool) : A :=
  ((if bit then 3/4 else 0):ℝ) • (1:A)+(1/4:ℝ) • b

theorem branch_cfc (b : A) (hb : IsSelfAdjoint b) (bit : Bool) :
    cfc (cantorBranch bit) b=branch b bit := by
  have he : cantorBranch bit=(fun x : ℝ => (if bit then 3/4 else 0)+(1/4)*x) := by
    funext x; unfold cantorBranch; ring
  rw [he,cfc_add b _ _ (by fun_prop) (by fun_prop),cfc_const _ b hb,
    cfc_const_mul_id _ b hb,Algebra.algebraMap_eq_smul_one]
  rfl

theorem block_function (a b p : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hpp : p*p=p) (hbp : b*p=p*b) (he : a=(1/4:ℝ) • b+(3/4:ℝ) • p)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f a=p*cfc f (branch b true)+(1-p)*cfc f (branch b false) := by
  have hi : a*p=p*branch b true := by
    rw [he]; simp only [branch,ite_true,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,mul_one,hpp,hbp]
    module
  have hj : a*(1-p)=(1-p)*branch b false := by
    rw [he]; simp only [branch,Bool.false_eq_true,ite_false,zero_smul,zero_add]
    simp only [add_mul,smul_mul_assoc,mul_smul_comm,mul_sub,sub_mul,mul_one,one_mul,hpp,hbp]
    module
  have hsa (bit : Bool) : IsSelfAdjoint (branch b bit) := by
    unfold branch
    exact ((IsSelfAdjoint.all _).smul (IsSelfAdjoint.one A)).add ((IsSelfAdjoint.all _).smul hb)
  have h1 := intertwines a (branch b true) p ha (hsa true) hi f hf
  have h0 := intertwines a (branch b false) (1-p) ha (hsa false) hj f hf
  calc
    _ = cfc f a*p+cfc f a*(1-p) := by noncomm_ring
    _ = _ := by rw [h1,h0]

theorem block_digit (a b p : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hσ : spectrum ℝ b ⊆ Set.Icc 0 1) (hpp : p*p=p) (hbp : b*p=p*b)
    (he : a=(1/4:ℝ) • b+(3/4:ℝ) • p) : cfc digitFunction a=p := by
  have h (bit : Bool) : cfc digitFunction (branch b bit)=
      ((if bit then 1 else 0):ℝ) • (1:A) := by
    rw [←branch_cfc b hb bit,←cfc_comp digitFunction (cantorBranch bit) b hb
      (digitFunction_lipschitz.continuous.continuousOn) (by unfold cantorBranch; fun_prop)]
    have hc : cfc (fun x => digitFunction (cantorBranch bit x)) b=
        cfc (fun _ : ℝ => if bit then 1 else 0) b :=
      cfc_congr (fun x hx => digitFunction_branch bit x (hσ hx))
    change cfc (fun x => digitFunction (cantorBranch bit x)) b=_
    rw [hc,cfc_const _ b hb,Algebra.algebraMap_eq_smul_one]
  rw [block_function a b p ha hb hpp hbp he _ digitFunction_lipschitz.continuous,h,h]
  simp

theorem block_distance (a b p : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hσ : spectrum ℝ b ⊆ Set.Icc 0 1) (hpp : p*p=p) (hbp : b*p=p*b)
    (he : a=(1/4:ℝ) • b+(3/4:ℝ) • p) :
    cfc (fun x => Metric.infDist x cantorSet) a=
      (1/4:ℝ) • cfc (fun x => Metric.infDist x cantorSet) b := by
  have h (bit : Bool) : cfc (fun x => Metric.infDist x cantorSet) (branch b bit)=
      (1/4:ℝ) • cfc (fun x => Metric.infDist x cantorSet) b := by
    rw [←branch_cfc b hb bit,←cfc_comp _ (cantorBranch bit) b hb
      cantor_distance_lipschitz.continuous.continuousOn (by unfold cantorBranch; fun_prop)]
    calc
      _=cfc (fun x : ℝ => (1/4)*Metric.infDist x cantorSet) b := by
        apply cfc_congr
        intro x hx
        simpa only [Function.comp_apply,one_div,one_mul,mul_comm,div_eq_mul_inv] using cantor_distance_branch bit x (hσ hx)
      _=_ := cfc_const_mul _ _ _
  rw [block_function a b p ha hb hpp hbp he _ cantor_distance_lipschitz.continuous,h,h]
  simp only [mul_smul_comm,sub_mul,one_mul]
  module

/-- Exact affine clocks already have Cantor spectrum and their first digit is p. -/
theorem affine (a p t : A) (ha : IsSelfAdjoint a)
    (hσ : spectrum ℝ a ⊆ Set.Icc 0 1) (hpp : p*p=p)
    (ht : star t*t=1 ∧ t*star t=1) (hap : a*p=p*a)
    (haff : t*a*star t=(4:ℂ) • a-(3:ℂ) • p) :
    spectrum ℝ a ⊆ cantorSet ∧ cfc digitFunction a=p ∧
      cfc tailFunction a=t*a*star t := by
  let b := t*a*star t
  have hb : IsSelfAdjoint b := by
    change star (t*a*star t)=t*a*star t
    simp only [star_mul,star_star,ha.star_eq,mul_assoc]
  have hσb : spectrum ℝ b ⊆ Set.Icc 0 1 := by
    let T : unitary A := ⟨t,ht⟩
    have he : spectrum ℝ b=spectrum ℝ a :=
      Unitary.spectrum_star_right_conjugate (U:=T)
    rw [he]; exact hσ
  have hbp : b*p=p*b := by
    dsimp [b]; rw [haff]
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,hap]
  have he : a=(1/4:ℝ) • b+(3/4:ℝ) • p := by
    dsimp [b]; rw [haff,real_smul,real_smul]
    norm_num
    module
  have hd := block_distance a b p ha hb hσb hpp hbp he
  have hconj := conjugate t a ht ha _ cantor_distance_lipschitz.continuous
  have hn : ‖t‖≤1 := by
    have hh := CStarRing.norm_star_mul_self (x:=t)
    rw [ht.1] at hh
    rcases subsingleton_or_nontrivial A with hA | hA
    · haveI := hA
      rw [Subsingleton.elim t 0,norm_zero]
      norm_num
    · haveI := hA
      norm_num at hh
      nlinarith [norm_nonneg t]
  have hn' : ‖star t‖≤1 := by simpa only [norm_star] using hn
  have hnD : ‖cfc (fun x => Metric.infDist x cantorSet) a‖=0 := by
    have heq : cfc (fun x => Metric.infDist x cantorSet) b=
        t*cfc (fun x => Metric.infDist x cantorSet) a*star t := hconj
    have hbound : ‖cfc (fun x => Metric.infDist x cantorSet) b‖≤
        ‖cfc (fun x => Metric.infDist x cantorSet) a‖ := by
      rw [heq]
      calc
        _ ≤ (‖t‖*‖cfc (fun x => Metric.infDist x cantorSet) a‖)*‖star t‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1*‖cfc (fun x => Metric.infDist x cantorSet) a‖*1 := by gcongr
        _ = _ := by ring
    have hh := congrArg norm hd
    rw [norm_smul] at hh
    norm_num at hh
    nlinarith [norm_nonneg (cfc (fun x => Metric.infDist x cantorSet) a)]
  have hz : cfc (fun x => Metric.infDist x cantorSet) a=cfc (fun _ : ℝ => 0) a := by
    change cfc (fun x => Metric.infDist x cantorSet) a=cfc (0:ℝ → ℝ) a
    rw [norm_eq_zero.mp hnD,cfc_zero]
  have hzero := eqOn_of_cfc_eq_cfc hz cantor_distance_lipschitz.continuous.continuousOn
    continuousOn_const ha
  refine ⟨?_,block_digit a b p ha hb hσb hpp hbp he,?_⟩
  · intro x hx
    exact (cantorSet_compact.isClosed.mem_iff_infDist_zero cantorSet_nonempty).mpr (hzero hx)
  · have hdigit := block_digit a b p ha hb hσb hpp hbp he
    have htail : tailFunction=(fun x : ℝ => 4*x-3*digitFunction x) := rfl
    rw [htail,cfc_sub (fun x : ℝ => 4*x) (fun x : ℝ => 3*digitFunction x) a (by fun_prop) (by exact continuousOn_const.mul digitFunction_lipschitz.continuous.continuousOn),
      cfc_const_mul_id _ a ha,cfc_const_mul (3:ℝ) digitFunction a digitFunction_lipschitz.continuous.continuousOn,hdigit,
      real_smul,real_smul]
    exact haff.symm
end
end E2.ExactClock






