import E2.CountCQ
import QIT.Information.Entropy.StrongSubadditivity

namespace E2.CountCQ
noncomputable section
open scoped BigOperators ComplexOrder NNReal

namespace Family
variable {ι κ ν a c b : Type*}
variable [Fintype ι] [Fintype κ] [Fintype ν] [Fintype a] [Fintype c] [Fintype b]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] [DecidableEq a] [DecidableEq c] [DecidableEq b]

@[ext] theorem ext (F G : Family ι b) (hm : F.mass=G.mass) (hA : F.matrix=G.matrix) : F=G := by
  cases F; cases G; cases hm; cases hA; rfl

def relabel (F : Family ι b) (e : κ ≃ ι) : Family κ b where
  mass x := F.mass (e x)
  matrix x := F.matrix (e x)
  nonneg x := F.nonneg (e x)
  positive x := F.positive (e x)
  trace x := F.trace (e x)
  total := (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans F.total

theorem relabel_conditional (F : Family ι b) (e : κ ≃ ι) (fallback : QIT.State b) :
    (F.relabel e).conditional fallback = F.conditional fallback := by
  have ha : (F.relabel e).average = F.average := by
    apply QIT.State.ext
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [conditional, conditional, ha]
  have hs : (F.relabel e).shannon=F.shannon :=
    congrArg (fun x => x / Real.log 2) (Fintype.sum_equiv e _ _ (fun _ => rfl))
  have hm : (F.relabel e).meanEntropy fallback=F.meanEntropy fallback :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hs,hm]

theorem coarse_relabel (F : Family ι b) (e : κ ≃ ι) (f : κ → ν) :
    (F.relabel e).coarse f = F.coarse (f ∘ e.symm) := by
  apply Family.ext
  · funext y
    exact Fintype.sum_equiv e _ _ (fun x => by simp [coarse, relabel])
  · funext y
    exact Fintype.sum_equiv e _ _ (fun x => by simp [coarse, relabel])

theorem sum_fiber_comp {A : Type*} [AddCommMonoid A] (v : ι → A) (f : ι → κ) (g : κ → ν) (z : ν) :
    (∑ y, if g y=z then (∑ x, if f x=y then v x else 0) else 0) = ∑ x, if g (f x)=z then v x else 0 := by
  calc
    _ = ∑ y, ∑ x, if f x=y then (if g y=z then v x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y=z <;> simp [h]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp

theorem coarse_coarse (F : Family ι b) (f : ι → κ) (g : κ → ν) :
    (F.coarse f).coarse g = F.coarse (g ∘ f) := by
  apply Family.ext
  · funext z
    exact sum_fiber_comp F.mass f g z
  · funext z
    exact sum_fiber_comp F.matrix f g z

theorem conditional_pair (F : Family (a × c) b) (fallback : QIT.State b) :
    F.conditional fallback ≤ (F.coarse Prod.fst).conditional fallback +
      (F.coarse Prod.snd).conditional fallback := by
  let rho := (F.ensemble fallback).cqState
  have hfst (x : a) : (F.coarse Prod.fst).matrix x = ∑ z : c,F.matrix (x,z) := by
    change (∑ r : a × c,if r.1=x then F.matrix r else 0) = _
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp
  have hAC : rho.marginalAC = ((F.coarse Prod.fst).ensemble fallback).cqState := by
    apply QIT.State.ext
    ext ⟨x,i⟩ ⟨y,j⟩
    change (∑ z : c, (F.ensemble fallback).cqState.matrix ((x,z),i) ((y,z),j)) = _
    simp only [cq_entry]
    by_cases h : x=y
    · subst y
      simp [hfst, Matrix.sum_apply]
    · simp [h]
  have hBC : rho.marginalBC = ((F.coarse Prod.snd).ensemble fallback).cqState := by
    apply QIT.State.ext
    ext ⟨x,i⟩ ⟨y,j⟩
    change (∑ z : a, (F.ensemble fallback).cqState.matrix ((z,x),i) ((z,y),j)) = _
    simp only [cq_entry]
    by_cases h : x=y
    · subst y
      simp [coarse, Fintype.sum_prod_type, Matrix.sum_apply, apply_ite]
    · simp [h]
  have hB : rho.marginalB = F.average :=
    (QIT.Ensemble.cqState_marginalB_eq_averageState _).trans (F.ensemble_average fallback)
  have hs := QIT.State.condMutualInfoABGivenC_nonneg rho
  rw [QIT.State.condMutualInfoABGivenC_eq, hAC, hBC, hB, cq_entropy, cq_entropy, cq_entropy] at hs
  unfold conditional
  rw [coarse_average, coarse_average]
  linarith

end Family

def headTailEquiv {n : ℕ} (α : Fin (n+1) → Type) :
    (α 0 × (∀ i : Fin n, α i.succ)) ≃ (∀ i, α i) where
  toFun x := Fin.cons x.1 x.2
  invFun x := (x 0, Fin.tail x)
  left_inv x := by simp
  right_inv x := by simp

theorem conditional_subadd (n : ℕ) (α : Fin n → Type) [∀ i, Fintype (α i)]
    [∀ i, DecidableEq (α i)] {b : Type} [Fintype b] [DecidableEq b]
    (F : Family (∀ i, α i) b) (fallback : QIT.State b) :
    F.conditional fallback ≤ ∑ i : Fin n, (F.coarse (fun x => x i)).conditional fallback := by
  classical
  induction n with
  | zero =>
    let a : ∀ i : Fin 0, α i := fun i => Fin.elim0 i
    letI : Unique (∀ i : Fin 0, α i) := ⟨⟨a⟩,fun x => Subsingleton.elim x a⟩
    have hm : F.mass default=1 := by simpa using F.total
    have hn : F.normalized fallback default=F.average := by
      apply QIT.State.ext
      simp [Family.normalized, Family.average, hm]
    simp [Family.conditional, Family.shannon, Family.meanEntropy, hm, hn]
  | succ n ih =>
    let e := headTailEquiv α
    let G := F.relabel e
    have hs := G.conditional_pair fallback
    have hi := ih (fun i => α i.succ) (F.coarse Fin.tail)
    have h0 : G.coarse Prod.fst=F.coarse (fun x => x 0) := by
      rw [Family.coarse_relabel]
      rfl
    have ht : G.coarse Prod.snd=F.coarse Fin.tail := by
      rw [Family.coarse_relabel]
      rfl
    have hg : G.conditional fallback=F.conditional fallback := F.relabel_conditional e fallback
    rw [hg,h0,ht] at hs
    simp only [Family.coarse_coarse, Function.comp_def, Fin.tail] at hi
    rw [Fin.sum_univ_succ]
    linarith

end
end E2.CountCQ

namespace E2
noncomputable section
open Turn9
open scoped BigOperators

theorem quantum_conditional_subadditivity : Turn9.QuantumConditionalSubadditivity := by
  intro d m s p
  have h := CountCQ.conditional_subadd m (fun i => Fin (p i).outcomes) (CountCQ.record s p) (CountCQ.original s)
  rw [CountCQ.record_conditional] at h
  simpa only [CountCQ.marginal_conditional] using h

end
end E2
