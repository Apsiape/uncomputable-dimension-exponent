import E2.CompilerBlocks

namespace E2.CompilerBlocks
variable {A : Type*} [Ring A] [StarRing A]

/-- The seven new reflections of the six-context gadget, exactly as displayed
in Section 3. Old reflections are repeated diagonally. -/
def sixExtension (a b c : A) : Fin 7 → Block A :=
  ![off a a, off 1 1, off b b, off (b*a) (a*b),
    diag (b*a*b) a, diag (b*c) 1, diag b c]

theorem six_extension (a b c : A) (ha : Reflection a) (hb : Reflection b)
    (hc : Reflection c) (hrel : a*b*a=c) (hbc : b*c=c*b) :
    (∀ i, Reflection (sixExtension a b c i)) ∧
    ParityTriple (diag a a) (sixExtension a b c 0) (sixExtension a b c 1) ∧
    ParityTriple (diag b b) (sixExtension a b c 1) (sixExtension a b c 2) ∧
    ParityTriple (sixExtension a b c 2) (sixExtension a b c 3) (sixExtension a b c 4) ∧
    ParityTriple (diag a a) (sixExtension a b c 4) (sixExtension a b c 5) ∧
    ParityTriple (diag c c) (sixExtension a b c 5) (sixExtension a b c 6) ∧
    ParityTriple (sixExtension a b c 0) (sixExtension a b c 3) (sixExtension a b c 6) := by
  have h₁ := reflection_off ha
  have h₂ : Reflection (off (1:A) 1) := reflection_off reflection_one
  have h₃ := reflection_off hb
  have h₄ : Reflection (off (b*a) (a*b)) := by
    constructor
    · simp [star_mul,ha.1,hb.1]
    · rw [off_mul_off]
      have hba : b*a*(a*b)=1 := by
        calc
          _ = b*(a*a)*b := by simp only [mul_assoc]
          _ = 1 := by rw [ha.2,mul_one,hb.2]
      have hab : a*b*(b*a)=1 := by
        calc
          _ = a*(b*b)*a := by simp only [mul_assoc]
          _ = 1 := by rw [hb.2,mul_one,ha.2]
      rw [hba,hab,diag_one]
  have h₅ := reflection_diag (reflection_conjugate hb ha) ha
  have h₆ := reflection_diag (reflection_product hb hc hbc) reflection_one
  have h₇ := reflection_diag hb hc
  have hAll : ∀ i, Reflection (sixExtension a b c i) := by
    intro i; fin_cases i <;> simp only [sixExtension,Matrix.cons_val_zero,Matrix.cons_val_succ] <;> assumption
  refine ⟨hAll,?_,?_,?_,?_,?_,?_⟩
  · apply parity_of_product (reflection_diag ha ha) h₁ h₂
    simp [sixExtension,ha.2]
  · apply parity_of_product (reflection_diag hb hb) h₂ h₃
    simp [sixExtension]
  · apply parity_of_product h₃ h₄ h₅
    simp only [sixExtension,Matrix.cons_val_zero,Matrix.cons_val_succ,off_mul_off]
    congr 1
    · simp only [mul_assoc]
    · rw [← mul_assoc,hb.2,one_mul]
  · apply parity_of_product (reflection_diag ha ha) h₅ h₆
    simp only [sixExtension,Matrix.cons_val_zero,Matrix.cons_val_succ,diag_mul_diag,ha.2]
    congr 1
    calc
      _ = (a*b*a)*b := by simp only [mul_assoc]
      _ = b*c := by rw [hrel,hbc]
  · apply parity_of_product (reflection_diag hc hc) h₆ h₇
    simp only [sixExtension,Matrix.cons_val_zero,Matrix.cons_val_succ,diag_mul_diag,mul_one]
    congr 1
    calc
      _ = (c*b)*c := by simp only [mul_assoc]
      _ = (b*c)*c := by rw [hbc]
      _ = b := by rw [mul_assoc,hc.2,mul_one]
  · apply parity_of_product h₁ h₄ h₇
    simp only [sixExtension,Matrix.cons_val_zero,Matrix.cons_val_succ,off_mul_off]
    congr 1
    · rw [← mul_assoc,ha.2,one_mul]
    · simpa only [mul_assoc] using hrel

def generalY (X : Fin 3 → A) (i : Fin 3) : Block A := diag (X i) 1
def generalZ (X : Fin 3 → A) (i : Fin 3) : Block A := diag 1 (X i)
def generalW (X : Fin 3 → A) (i : Fin 3) : Block A := off (X i) (X i)

/-- Exact doubled extension of the general conjugacy gadget, including the
commutation of the targets of all remaining conjugacies. -/
theorem general_extension (X : Fin 3 → A) (hX : ∀ i, Reflection (X i))
    (hrel : X 0*X 1*X 0=X 2) :
    Reflection (off (1:A) 1) ∧ Reflection (diag (X 1) (X 2)) ∧
    (∀ i, Reflection (generalY X i) ∧ Reflection (generalZ X i) ∧ Reflection (generalW X i)) ∧
    (∀ i, ParityTriple (diag (X i) (X i)) (generalY X i) (generalZ X i)) ∧
    (∀ i, ParityTriple (diag (X i) (X i)) (off 1 1) (generalW X i)) ∧
    ParityTriple (diag (X 1) (X 2)) (generalY X 1) (generalZ X 2) ∧
    (∀ i, off 1 1*generalY X i*off 1 1=generalZ X i) ∧
    generalW X 0*generalY X 1*generalW X 0=generalZ X 2 ∧
    (∀ i, generalY X i*generalZ X i=generalZ X i*generalY X i) ∧
    generalY X 1*generalZ X 2=generalZ X 2*generalY X 1 := by
  have hf : Reflection (off (1:A) 1) := reflection_off reflection_one
  have hy (i : Fin 3) : Reflection (generalY X i) := reflection_diag (hX i) reflection_one
  have hz (i : Fin 3) : Reflection (generalZ X i) := reflection_diag reflection_one (hX i)
  have hw (i : Fin 3) : Reflection (generalW X i) := reflection_off (hX i)
  refine ⟨hf,reflection_diag (hX 1) (hX 2),fun i => ⟨hy i,hz i,hw i⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    apply parity_of_product (reflection_diag (hX i) (hX i)) (hy i) (hz i)
    simp [generalY,generalZ,(hX i).2]
  · intro i
    apply parity_of_product (reflection_diag (hX i) (hX i)) hf (hw i)
    simp [generalW]
  · apply parity_of_product (reflection_diag (hX 1) (hX 2)) (hy 1) (hz 2)
    simp [generalY,generalZ,(hX 1).2]
  · intro i
    simp [generalY,generalZ]
  · simp [generalW,generalY,generalZ,(hX 0).2,hrel]
  · intro i
    simp [generalY,generalZ]
  · simp [generalY,generalZ]

end E2.CompilerBlocks
