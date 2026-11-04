import E2.CompilerFrontend

namespace E2.CompilerWords
noncomputable section
open scoped BigOperators
variable {ι : Type*}

abbrev WordSum (ι : Type*) := List (ℚ × List ι)

def multiply (xs ys : WordSum ι) : WordSum ι :=
  xs.flatMap (fun x => ys.map (fun y => (x.1*y.1,x.2++y.2)))

def normalForm : Poly ι → WordSum ι
  | .const q => [(q,[])]
  | .var i => [(1,[i])]
  | .add p q => normalForm p ++ normalForm q
  | .mul p q => multiply (normalForm p) (normalForm q)
  | .adj p => (normalForm p).map (fun t => (t.1,t.2.reverse))

def wordEval {d : ℕ} (x : ι → Mat d) (w : List ι) : Mat d := (w.map x).prod

def sumEval {d : ℕ} (x : ι → Mat d) (xs : WordSum ι) : Mat d :=
  (xs.map (fun t => (t.1 : ℂ) • wordEval x t.2)).sum

@[simp] theorem wordEval_append {d : ℕ} (x : ι → Mat d) (u v : List ι) :
    wordEval x (u++v)=wordEval x u*wordEval x v := by simp [wordEval]

theorem wordEval_adjoint {d : ℕ} (x : ι → Mat d)
    (hx : ∀ i, Domain.reflection.Holds (x i)) (w : List ι) :
    (wordEval x w).conjTranspose=wordEval x w.reverse := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    simpa only [wordEval,List.map_cons,List.prod_cons,Matrix.conjTranspose_mul,
      (hx i).1,List.reverse_cons,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton,List.map_nil,List.prod_nil,Matrix.mul_one]
      using congrArg (fun M => M*x i) ih

@[simp] theorem sumEval_append {d : ℕ} (x : ι → Mat d) (u v : WordSum ι) :
    sumEval x (u++v)=sumEval x u+sumEval x v := by simp [sumEval]

@[simp] theorem sumEval_nil {d : ℕ} (x : ι → Mat d) : sumEval x []=0 := rfl
@[simp] theorem sumEval_cons {d : ℕ} (x : ι → Mat d) (t : ℚ × List ι) (xs : WordSum ι) :
    sumEval x (t::xs)=(t.1:ℂ) • wordEval x t.2+sumEval x xs := rfl

theorem sumEval_left_word {d : ℕ} (x : ι → Mat d) (t : ℚ × List ι) (v : WordSum ι) :
    sumEval x (v.map (fun y => (t.1*y.1,t.2++y.2))) =
      ((t.1:ℂ) • wordEval x t.2)*sumEval x v := by
  induction v with
  | nil => simp
  | cons y v jh =>
    simp only [List.map_cons,sumEval_cons]
    rw [jh,Matrix.mul_add]
    congr 1
    simp only [wordEval_append,Rat.cast_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [mul_comm (t.1:ℂ) (y.1:ℂ)]

theorem sumEval_multiply {d : ℕ} (x : ι → Mat d) (u v : WordSum ι) :
    sumEval x (multiply u v)=sumEval x u*sumEval x v := by
  induction u with
  | nil => simp [multiply]
  | cons t u ih =>
    change sumEval x (v.map (fun y => (t.1*y.1,t.2++y.2)) ++ multiply u v)=_
    rw [sumEval_append,sumEval_left_word,ih,sumEval_cons,Matrix.add_mul]

/-- Every rational real-coefficient *-polynomial on reflections is a finite
rational linear combination of reflection words, including all adjoints. -/
theorem eval_normalForm {d : ℕ} (x : ι → Mat d)
    (hx : ∀ i, Domain.reflection.Holds (x i)) (p : Poly ι) :
    sumEval x (normalForm p)=Poly.eval x p := by
  induction p with
  | const q => simp [normalForm,sumEval,wordEval,Poly.eval]
  | var i => simp [normalForm,sumEval,wordEval,Poly.eval]
  | add p q hp hq => simpa only [normalForm,sumEval_append,Poly.eval] using congrArg₂ (·+·) hp hq
  | mul p q hp hq => simpa only [normalForm,sumEval_multiply,Poly.eval] using congrArg₂ (·*·) hp hq
  | adj p hp =>
    rw [normalForm]
    have he : sumEval x ((normalForm p).map (fun t => (t.1,t.2.reverse))) =
        (sumEval x (normalForm p)).conjTranspose := by
      simp only [sumEval,List.map_map,Function.comp_apply,Matrix.conjTranspose_list_sum]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp [Matrix.conjTranspose_smul,wordEval_adjoint x hx]
    rw [he,hp]
    rfl

end
end E2.CompilerWords
