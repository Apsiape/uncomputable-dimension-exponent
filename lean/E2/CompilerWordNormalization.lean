import E2.CompilerNormalizedRealize

namespace E2.CompilerNetwork
noncomputable section
open scoped BigOperators
open E2.CompilerRealize E2.CompilerUniversal E2.CompilerPolynomial
open CompilerMultiSelector (polyProduct polySum)

variable {κ : Type*} {G : BCSGame}

def wordPolynomial (v : κ → Fin G.numVars) (w : List κ) : Poly (Fin G.numVars) :=
  polyProduct (w.map (fun i => .var (v i)))

def linearPolynomial (v : κ → Fin G.numVars) (ws : CompilerWords.WordSum κ) : Poly (Fin G.numVars) :=
  polySum (ws.map (fun t => .const t.1 * wordPolynomial v t.2))

@[simp] theorem image_word (G : BCSGame) (v : κ → Fin G.numVars) (w : List κ) :
    image (augmented G).relations (wordPolynomial v w) = word (generator G ∘ v) w := by
  simp [wordPolynomial,CompilerMultiSelector.image_product,word,generator,Function.comp_def]

@[simp] theorem image_linear (G : BCSGame) (v : κ → Fin G.numVars) (ws : CompilerWords.WordSum κ) :
    image (augmented G).relations (linearPolynomial v ws) = linearSum (generator G ∘ v) ws := by
  simp only [linearPolynomial,CompilerMultiSelector.image_sum,List.map_map,Function.comp_def,
    image_scale,image_word,linearSum]

theorem adjoint_image_congr (G : BCSGame) (p q : Poly (Fin G.numVars))
    (h : image (augmented G).relations p = image (augmented G).relations q) :
    image (augmented G).relations p.adj = image (augmented G).relations q.adj := by
  have hz : image (augmented G).relations (p-q)=0 := by simpa using sub_eq_zero.mpr h
  obtain ⟨D⟩ := (image_eq_zero_iff _ _).mp hz
  have ha := (image_eq_zero_iff _ _).mpr ⟨D.adj⟩
  have he := image_semantic (augmented G).relations (p-q).adj (p.adj-q.adj) (by
    intro d x
    simp [Poly.eval_sub,Poly.eval,Matrix.conjTranspose_sub])
  rw [he,image_sub] at ha
  exact sub_eq_zero.mp ha

theorem image_adj_mul (G : BCSGame) (p q : Poly (Fin G.numVars)) :
    image (augmented G).relations (p*q).adj =
      image (augmented G).relations q.adj * image (augmented G).relations p.adj := by
  rw [← image_mul]
  apply image_semantic
  intro d x
  simp [Poly.eval,Matrix.conjTranspose_mul]

theorem image_adj_add (G : BCSGame) (p q : Poly (Fin G.numVars)) :
    image (augmented G).relations (p+q).adj =
      image (augmented G).relations p.adj + image (augmented G).relations q.adj := by
  rw [← image_add]
  apply image_semantic
  intro d x
  simp [Poly.eval,Matrix.conjTranspose_add]

theorem image_adj_const (G : BCSGame) (c : ℚ) :
    image (augmented G).relations (Poly.const c).adj = image (augmented G).relations (.const c) := by
  apply image_semantic
  intro d x
  simp [Poly.eval,Matrix.conjTranspose_smul]

theorem image_adj_word (G : BCSGame) (v : κ → Fin G.numVars) (w : List κ) :
    image (augmented G).relations (wordPolynomial v w).adj =
      word (generator G ∘ v) w.reverse := by
  induction w with
  | nil => exact (image_adj_const G 1).trans (by simp [word])
  | cons i w ih =>
    change image _ (Poly.var (v i) * wordPolynomial v w).adj = _
    rw [image_adj_mul,ih,variable_adjoint]
    simp only [List.reverse_cons,word,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,Function.comp_apply]

theorem image_adj_linear (G : BCSGame) (v : κ → Fin G.numVars) (ws : CompilerWords.WordSum κ) :
    image (augmented G).relations (linearPolynomial v ws).adj =
      linearSum (generator G ∘ v) (ws.map (fun t => (t.1,t.2.reverse))) := by
  induction ws with
  | nil => exact (image_adj_const G 0).trans (by simp [linearSum])
  | cons t ws ih =>
    change image _ (.const t.1 * wordPolynomial v t.2 + linearPolynomial v ws).adj = _
    rw [image_adj_add,image_adj_mul,image_adj_word,image_adj_const,image_const,ih]
    simp only [linearSum,List.map_cons,List.sum_cons]
    congr 1
    exact (Algebra.commutes t.1 _).symm.trans (Algebra.smul_def _ _).symm

section RingWords
variable {A : Type*} [Ring A] [Algebra ℚ A]

omit [Algebra ℚ A] in
@[simp] theorem word_append (x : κ → A) (u v : List κ) : word x (u++v)=word x u*word x v := by
  simp [word]

@[simp] theorem linearSum_append (x : κ → A) (u v : CompilerWords.WordSum κ) :
    linearSum x (u++v)=linearSum x u+linearSum x v := by simp [linearSum]

theorem linearSum_multiply (x : κ → A) (u v : CompilerWords.WordSum κ) :
    linearSum x (CompilerWords.multiply u v)=linearSum x u*linearSum x v := by
  have ht (t : ℚ × List κ) :
      linearSum x (v.map (fun y => (t.1*y.1,t.2++y.2))) =
        (t.1 • word x t.2)*linearSum x v := by
    induction v with
    | nil => simp [linearSum]
    | cons y v ih =>
      simp only [List.map_cons,linearSum,List.sum_cons] at ih ⊢
      rw [mul_add,← ih]
      congr 1
      simp only [word_append,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
      rw [mul_comm t.1 y.1]
  induction u with
  | nil => simp [CompilerWords.multiply,linearSum]
  | cons t u ih =>
    change linearSum x (v.map (fun y => (t.1*y.1,t.2++y.2)) ++ CompilerWords.multiply u v) = _
    rw [linearSum_append,ht,ih]
    simp [linearSum,add_mul]
end RingWords

/-- Reflection-word normalization in the finite-certificate quotient, including adjoints. -/
theorem normalForm_image (G : BCSGame) (v : κ → Fin G.numVars) (p : Poly κ) :
    linearSum (generator G ∘ v) (CompilerWords.normalForm p) =
      image (augmented G).relations (CompilerFrontend.substitute (fun i => .var (v i)) p) := by
  induction p with
  | const c => simp [CompilerWords.normalForm,linearSum,word,CompilerFrontend.substitute,Algebra.smul_def]
  | var i => simp [CompilerWords.normalForm,linearSum,word,CompilerFrontend.substitute,generator,Function.comp_def]
  | add p q hp hq => simpa only [CompilerWords.normalForm,linearSum_append,
      CompilerFrontend.substitute,image_add] using congrArg₂ (·+·) hp hq
  | mul p q hp hq => simpa only [CompilerWords.normalForm,linearSum_multiply,
      CompilerFrontend.substitute,image_mul] using congrArg₂ (·*·) hp hq
  | adj p hp =>
    change linearSum _ ((CompilerWords.normalForm p).map _) = _
    rw [← image_adj_linear]
    apply adjoint_image_congr
    simpa only [image_linear] using hp

end
end E2.CompilerNetwork

