import E2.FeasibilityRaw
import E2.EffectiveSearch

namespace E2.FeasibilityComputation
open E2.RealArithmetic E2.FeasibilitySentence Primrec

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

theorem pr_fst {f : α → β × γ} (h : Primrec f) : Primrec (fun x => (f x).1) := fst.comp h
theorem pr_snd {f : α → β × γ} (h : Primrec f) : Primrec (fun x => (f x).2) := snd.comp h
theorem pr_pair {f : α → β} {g : α → γ} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => (f x,g x)) := hf.pair hg
theorem pr_encode {f : α → β} (hf : Primrec f) : Primrec (fun x => Encodable.encode (f x)) := Primrec.encode.comp hf
theorem pr_inl {f : α → β} (hf : Primrec f) : Primrec (fun x => (Sum.inl (f x) : β ⊕ γ)) := sumInl.comp hf
theorem pr_inr {f : α → γ} (hf : Primrec f) : Primrec (fun x => (Sum.inr (f x) : β ⊕ γ)) := sumInr.comp hf

theorem cvar_primrec : Primrec cvar := by
  exact ((var_primrec.comp (nat_mul.comp (const 2) .id)).pair
    (var_primrec.comp (nat_add.comp (nat_mul.comp (const 2) .id) (const 1))))
theorem cadd_primrec : Primrec₂ cadd :=
  (add_primrec.comp (fst.comp fst) (fst.comp snd)).pair
    (add_primrec.comp (snd.comp fst) (snd.comp snd))
theorem cmul_primrec : Primrec₂ cmul :=
  (sub_primrec.comp (mul_primrec.comp (fst.comp fst) (fst.comp snd))
    (mul_primrec.comp (snd.comp fst) (snd.comp snd))).pair
  (add_primrec.comp (mul_primrec.comp (fst.comp fst) (snd.comp snd))
    (mul_primrec.comp (snd.comp fst) (fst.comp snd)))
theorem cstar_primrec : Primrec cstar := fst.pair (neg_primrec.comp snd)
theorem csum_primrec : Primrec csum :=
  (sum_primrec.comp (list_map .id (fst.comp snd).to₂)).pair
    (sum_primrec.comp (list_map .id (snd.comp snd).to₂))
theorem ceq_primrec : Primrec₂ ceq := by
  exact list_cons.comp ((const true).pair (sub_primrec.comp (fst.comp fst) (fst.comp snd)))
    (list_cons.comp ((const true).pair (sub_primrec.comp (snd.comp fst) (snd.comp snd))) (const []))

theorem pr_cvar {f : α → ℕ} (h : Primrec f) : Primrec (fun x => cvar (f x)) := cvar_primrec.comp h
theorem pr_cmul {f g : α → CPoly} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => cmul (f x) (g x)) := cmul_primrec.comp hf hg
theorem pr_cstar {f : α → CPoly} (h : Primrec f) : Primrec (fun x => cstar (f x)) := cstar_primrec.comp h
theorem pr_csum {f : α → List CPoly} (h : Primrec f) : Primrec (fun x => csum (f x)) := csum_primrec.comp h
theorem pr_ceq {f g : α → CPoly} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => ceq (f x) (g x)) := ceq_primrec.comp hf hg
theorem pr_sub {f g : α → RealArithmetic.Poly} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => sub (f x) (g x)) := sub_primrec.comp hf hg
theorem pr_constant {f : α → ℚ} (h : Primrec f) : Primrec (fun x => constant (f x)) := constant_primrec.comp h
theorem pr_append {f g : α → Sentence} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x ++ g x) := list_append.comp hf hg
theorem pr_cons {f : α → β} {g : α → List β} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x :: g x) := list_cons.comp hf hg

theorem pr_rAll {n : α → ℕ} {f : α → ℕ → Sentence} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec (fun x => rAll (n x) (f x)) := list_flatMap (list_range.comp hn) hf

theorem pr_rTotal {n : α → ℕ} {f : α → ℕ → CPoly} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec (fun x => rTotal (n x) (f x)) := csum_primrec.comp (list_map (list_range.comp hn) hf)

theorem pr_fixed_map {ι : Type*} (xs : List ι) (f : α → ι → β) (hf : ∀ i, Primrec (fun x => f x i)) :
    Primrec (fun x => xs.map (f x)) := by
  induction xs with
  | nil => exact const []
  | cons i xs ih => exact list_cons.comp (hf i) ih

theorem pr_fixed_all {ι : Type*} [Fintype ι] (E : Enumeration ι) (f : α → ι → Sentence)
    (hf : ∀ i, Primrec (fun x => f x i)) : Primrec (fun x => all E (f x)) :=
  list_flatten.comp (pr_fixed_map E.entries f hf)

theorem pr_fixed_total {ι : Type*} [Fintype ι] (E : Enumeration ι) (f : α → ι → CPoly)
    (hf : ∀ i, Primrec (fun x => f x i)) : Primrec (fun x => total E (f x)) :=
  csum_primrec.comp (pr_fixed_map E.entries f hf)

theorem pr_rIdentity {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => rIdentity (f x) (g x)) := ite (Primrec.eq.comp hf hg) (const cone) (const czero)

theorem pr_natPair {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => Nat.pair (f x) (g x)) := Primrec₂.natPair.comp hf hg
theorem pr_natAdd {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x + g x) := nat_add.comp hf hg
theorem pr_natMul {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x * g x) := nat_mul.comp hf hg

theorem pr_map {f : α → List β} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun x => (f x).map (g x)) := list_map hf hg

theorem pr_flatMap {f : α → List β} {g : α → β → List γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun x => (f x).flatMap (g x)) := list_flatMap hf hg

theorem pr_cconst {f : α → ℚ} (hf : Primrec f) : Primrec (fun x => cconst (f x)) :=
  (constant_primrec.comp hf).pair (const (constant 0))

syntax "code_primrec" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
| `(tactic| code_primrec) => do
  try
    evalTactic (← `(tactic| first | assumption | with_reducible exact Primrec.id | with_reducible exact Primrec.fst | with_reducible exact Primrec.snd | with_reducible exact Primrec.const _))
    return
  catch _ => pure ()
  let mut t ← instantiateMVars (← getMainTarget)
  if t.isAppOf ``Primrec₂ then
    evalTactic (← `(tactic| unfold Primrec₂))
    t ← instantiateMVars (← getMainTarget)
  evalTactic (← `(tactic| try dsimp only [rAll₂,rTotal₂]))
  t ← instantiateMVars (← getMainTarget)
  let f := t.getAppArgs.back!
  let head ← lambdaTelescope (← whnf f) fun _ body => pure body.headBeta.getAppFn.constName?
  if head == some ``Nat.pair then evalTactic (← `(tactic| apply pr_natPair <;> code_primrec))
  else if head == some ``HAdd.hAdd then evalTactic (← `(tactic| apply pr_natAdd <;> code_primrec))
  else if head == some ``HMul.hMul then evalTactic (← `(tactic| apply pr_natMul <;> code_primrec))
  else if head == some ``rAll then evalTactic (← `(tactic| apply pr_rAll <;> code_primrec))
  else if head == some ``rTotal then evalTactic (← `(tactic| apply pr_rTotal <;> code_primrec))
  else if head == some ``all then evalTactic (← `(tactic| apply pr_fixed_all; intro i; code_primrec))
  else if head == some ``total then evalTactic (← `(tactic| apply pr_fixed_total; intro i; code_primrec))
  else if head == some ``List.map then evalTactic (← `(tactic| first
    | (apply pr_fixed_map; intro i; code_primrec)
    | (apply pr_map <;> code_primrec)))
  else if head == some ``List.flatMap then evalTactic (← `(tactic| apply pr_flatMap <;> code_primrec))
  else if head == some ``cconst then evalTactic (← `(tactic| apply pr_cconst; code_primrec))
  else if head == some ``rIdentity then evalTactic (← `(tactic| apply pr_rIdentity <;> code_primrec))
  else if head == some ``ceq then evalTactic (← `(tactic| apply pr_ceq <;> code_primrec))
  else if head == some ``cmul then evalTactic (← `(tactic| apply pr_cmul <;> code_primrec))
  else if head == some ``cstar then evalTactic (← `(tactic| apply pr_cstar; code_primrec))
  else if head == some ``csum then evalTactic (← `(tactic| apply pr_csum; code_primrec))
  else if head == some ``cvar then evalTactic (← `(tactic| apply pr_cvar; code_primrec))
  else if head == some ``sub then evalTactic (← `(tactic| apply pr_sub <;> code_primrec))
  else if head == some ``constant then evalTactic (← `(tactic| apply pr_constant; code_primrec))
  else if head == some ``HAppend.hAppend then evalTactic (← `(tactic| apply pr_append <;> code_primrec))
  else if head == some ``List.cons then evalTactic (← `(tactic| apply pr_cons <;> code_primrec))
  else if head == some ``Prod.mk then evalTactic (← `(tactic| apply pr_pair <;> code_primrec))
  else if head == some ``Sum.inl then evalTactic (← `(tactic| apply pr_inl; code_primrec))
  else if head == some ``Sum.inr then evalTactic (← `(tactic| apply pr_inr; code_primrec))
  else if head == some ``Encodable.encode then evalTactic (← `(tactic| apply pr_encode; code_primrec))
  else if head == some ``Prod.fst then evalTactic (← `(tactic| apply pr_fst; code_primrec))
  else if head == some ``Prod.snd then evalTactic (← `(tactic| apply pr_snd; code_primrec))
  else throwError "unsupported code head {head}: {t}"

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
theorem rConstraints_primrec (G : BCSGame) : Primrec (fun p : ℚ × ℕ => rConstraints G p.1 p.2) := by
  classical
  unfold rConstraints rAll₂ rTotal₂ rEq rGram rRGram rWinning rR rA rB
  simp only [Encodable.encode_prod_val,Encodable.encode_inl,Encodable.encode_inr,Encodable.encode_nat]
  code_primrec

theorem sentence_primrec (G : BCSGame) : Primrec (fun p : ℚ × ℕ => sentence G p.1 p.2) := by
  have h : Primrec (fun p : ℚ × ℕ => rSentence G p.1 p.2) :=
    ite (Primrec.eq.comp snd (const 0)) (const _) (rConstraints_primrec G)
  exact h.of_eq (fun p => (sentence_eq_raw G p.1 p.2).symm)

theorem feasible_decision (hT : TarskiDecision) (G : BCSGame) :
    ComputablePred (fun nd : ℕ × ℕ => Feasible G (rationalCode nd.1) nd.2) := by
  have hf : Computable (fun nd : ℕ × ℕ => sentence G (rationalCode nd.1) nd.2) :=
    (sentence_primrec G).to_comp.comp ((EffectiveCoding.rational_decode.to_comp.comp Computable.fst).pair Computable.snd)
  classical
  have hh : ComputablePred (fun nd : ℕ × ℕ => Truth (sentence G (rationalCode nd.1) nd.2)) :=
    Computable.computablePred ((conjunction_decision hT).decide.comp hf)
  exact hh.of_eq (fun nd => truth_iff_feasible G (rationalCode nd.1) nd.2)

theorem fixed_precision (hT : TarskiDecision) (G : BCSGame) (hG : quantumValue G = 1) :
    Computable (fun n : ℕ => if 0 < rationalCode n then
      (dimension G (rationalCode n)).toNat else 0) :=
  EffectiveSearch.fixed_precision_of_decision G hG (feasible_decision hT G)

end E2.FeasibilityComputation
