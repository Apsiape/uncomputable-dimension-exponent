import E2.CounterStackPop

namespace E2.CounterTermination
open Relation StateTransition
variable {Q V : Type*}


def next (f : (Option Q × V) → (Option Q × V)) (c : (Option Q × V)) : Option (Option Q × V) :=
  match c.1 with
  | none => none
  | some _ => some (f c)

@[simp] theorem next_eq_none (f : (Option Q × V) → (Option Q × V)) (c : (Option Q × V)) :
    next f c = none ↔ c.1 = none := by cases hc : c.1 <;> simp [next,hc]

theorem next_mem {f : (Option Q × V) → (Option Q × V)} {a b : (Option Q × V)} (h : b ∈ next f a) : f a = b := by
  cases ha : a.1 <;> simp [next,ha] at h
  exact h

theorem dom_iff (f : (Option Q × V) → (Option Q × V)) (c : (Option Q × V)) :
    (eval (next f) c).Dom ↔ ∃ t, (f^[t] c).1 = none := by
  constructor
  · intro hc
    obtain ⟨h,hterm⟩ := mem_eval.mp (Part.get_mem hc)
    have total : ∀ {a b}, Reaches (next f) a b → ∃ t, f^[t] a = b := by
      intro a b hr
      induction hr with
      | refl => exact ⟨0,rfl⟩
      | tail hab hbd ih =>
        obtain ⟨t,ht⟩ := ih
        exact ⟨t+1,by rw [Function.iterate_succ_apply',ht]; exact next_mem hbd⟩
    have hiter := total h
    obtain ⟨t,ht⟩ := hiter
    exact ⟨t,ht ▸ (next_eq_none f _).mp hterm⟩
  · rintro ⟨t,ht⟩
    induction t generalizing c with
    | zero =>
      exact (mem_eval.mpr ⟨.refl,(next_eq_none f c).mpr ht⟩ : c ∈ eval (next f) c).1
    | succ t ih =>
      by_cases hc : c.1 = none
      · exact (mem_eval.mpr ⟨.refl,(next_eq_none f c).mpr hc⟩ : c ∈ eval (next f) c).1
      · have hd : (eval (next f) (f c)).Dom := ih (f c) (by
          simpa only [Function.iterate_succ_apply] using ht)
        have hstep : f c ∈ next f c := by
          cases hq : c.1 <;> simp_all [next]
        rw [reaches_eval (ReflTransGen.single hstep)]
        exact hd

theorem reach_of_total (f : (Option Q × V) → (Option Q × V)) (hstop : ∀ v, f (none,v) = (none,v))
    {a b : (Option Q × V)} (h : ReflTransGen (fun x y => f x = y) a b) (hb : b.1 ≠ none) :
    Reaches (next f) a b := by
  have terminal : ∀ {v b}, ReflTransGen (fun x y => f x = y) (none,v) b → b = (none,v) := by
    intro v b hr
    induction hr with
    | refl => rfl
    | tail hab hbc ih => rw [ih,hstop] at hbc; exact hbc.symm
  induction h using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a d had hdb ih =>
    have ha : a.1 ≠ none := by
      intro hh
      have he : a = (none,a.2) := Prod.ext hh rfl
      have hfull : ReflTransGen (fun x y => f x = y) a b := .head had hdb
      rw [he] at hfull
      have hh := terminal hfull
      exact hb (congrArg Prod.fst hh)
    have hstep : d ∈ next f a := by
      cases hq : a.1 <;> simp_all [next]
    exact ReflTransGen.head hstep ih

end E2.CounterTermination