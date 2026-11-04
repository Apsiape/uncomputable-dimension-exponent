import E2.ExactModelDefs

namespace E2.Poly
noncomputable section
variable {A ι : Type*} [CStarAlgebra A] (x : ι → A)
@[simp] theorem evalC_add (p q : Poly ι) : evalC x (p+q)=evalC x p+evalC x q := rfl
@[simp] theorem evalC_mul (p q : Poly ι) : evalC x (p*q)=evalC x p*evalC x q := rfl
@[simp] theorem evalC_adj (p : Poly ι) : evalC x p.adj=star (evalC x p) := rfl
@[simp] theorem evalC_const (q : ℚ) : evalC x (.const q)=(q:ℂ) • (1:A) := rfl
@[simp] theorem evalC_var (i : ι) : evalC x (.var i)=x i := rfl
@[simp] theorem evalC_neg (p : Poly ι) : evalC x (-p)= -evalC x p := by
  change evalC x ((.const (-1))*p)=_
  rw [evalC_mul,evalC_const]
  simp
@[simp] theorem evalC_sub (p q : Poly ι) : evalC x (p-q)=evalC x p-evalC x q := by
  change evalC x (p+(-q))=_
  rw [evalC_add,evalC_neg,sub_eq_add_neg]
@[simp] theorem evalC_zero : evalC x (0:Poly ι)=0 := by change evalC x (.const 0)=_; rw [evalC_const]; simp
@[simp] theorem evalC_one : evalC x (1:Poly ι)=1 := by change evalC x (.const 1)=_; rw [evalC_const]; simp
@[simp] theorem evalC_three : evalC x (3:Poly ι)=(3:ℂ) • (1:A) := rfl
@[simp] theorem evalC_four : evalC x (4:Poly ι)=(4:ℂ) • (1:A) := rfl

end
end E2.Poly
