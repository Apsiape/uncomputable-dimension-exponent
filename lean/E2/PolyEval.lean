import E2.Presentation

namespace E2.Poly
noncomputable section
variable {ι : Type*} {d : ℕ} (x : ι → Mat d)

@[simp] theorem eval_add (p q : Poly ι) : eval x (p+q)=eval x p+eval x q := rfl
@[simp] theorem eval_mul (p q : Poly ι) : eval x (p*q)=eval x p*eval x q := rfl
@[simp] theorem eval_adj (p : Poly ι) : eval x p.adj=(eval x p).conjTranspose := rfl
@[simp] theorem eval_const (q : ℚ) : eval x (.const q)=(q:ℂ) • (1:Mat d) := rfl
@[simp] theorem eval_var (i : ι) : eval x (.var i)=x i := rfl
@[simp] theorem eval_neg (p : Poly ι) : eval x (-p)= -eval x p := by
  change eval x ((.const (-1))*p)=_
  rw [eval_mul,eval_const]
  simp
@[simp] theorem eval_sub (p q : Poly ι) : eval x (p-q)=eval x p-eval x q := by
  change eval x (p+(-q))=_
  rw [eval_add,eval_neg,sub_eq_add_neg]
@[simp] theorem eval_zero : eval x (0:Poly ι)=0 := by change eval x (.const 0)=_; rw [eval_const]; simp
@[simp] theorem eval_one : eval x (1:Poly ι)=1 := by change eval x (.const 1)=_; rw [eval_const]; simp
@[simp] theorem eval_three : eval x (3:Poly ι)=(3:ℂ) • (1:Mat d) := rfl
@[simp] theorem eval_four : eval x (4:Poly ι)=(4:ℂ) • (1:Mat d) := rfl

end
end E2.Poly
