import E2.FiniteCarryFunctions

namespace E2.FiniteConstruction
noncomputable section

def listDecodeL : List (Fin 4) → Bool
  | [] => false
  | a::as => if a=0 then listDecodeL as else decide (a=1)

def listDecodeR : List (Fin 4) → ℝ
  | [] => 0
  | a::as => if a=0 then (1/2:ℝ)*listDecodeR as else 1

theorem listDecodeL_append_zero (as : List (Fin 4)) :
    listDecodeL (as++[0]) = listDecodeL as := by
  induction as with
  | nil => simp [listDecodeL]
  | cons a as ih => by_cases h : a=0 <;> simp [listDecodeL,h,ih]

theorem listDecodeR_append_zero (as : List (Fin 4)) :
    listDecodeR (as++[0]) = listDecodeR as := by
  induction as with
  | nil => simp [listDecodeR]
  | cons a as ih => by_cases h : a=0 <;> simp [listDecodeR,h,ih]

theorem listDecodeL_rotation (a : Fin 4) (as : List (Fin 4)) :
    listDecodeL (a::as) =
      if a=0 then listDecodeL (listRotate (a::as)) else decide (a=1) := by
  by_cases h : a=0
  · subst a
    simp [listDecodeL,listRotate,listDecodeL_append_zero]
  · simp [listDecodeL,h]

theorem listDecodeR_rotation (a : Fin 4) (as : List (Fin 4)) :
    listDecodeR (a::as) =
      if a=0 then (1/2:ℝ)*listDecodeR (listRotate (a::as)) else 1 := by
  by_cases h : a=0
  · subst a
    simp [listDecodeR,listRotate,listDecodeR_append_zero]
  · simp [listDecodeR,h]

theorem listDecodeR_bounds (as : List (Fin 4)) :
    0 ≤ listDecodeR as ∧ listDecodeR as ≤ 1 := by
  induction as with
  | nil => simp [listDecodeR]
  | cons a as ih =>
    by_cases h : a=0 <;> simp only [listDecodeR,h,↓reduceIte]
    · constructor <;> nlinarith [ih.1,ih.2]
    · exact ⟨by norm_num,le_rfl⟩

theorem listDecode_prefix (e : ℕ) (as : List (Fin 4)) :
    listDecodeL (List.replicate e 0 ++ 1::as) = true ∧
      listDecodeR (List.replicate e 0 ++ 1::as) = (1/2:ℝ)^e := by
  induction e with
  | zero => norm_num [listDecodeL,listDecodeR]
  | succ e ih =>
    simp only [List.replicate_succ,List.cons_append,listDecodeL,listDecodeR,↓reduceIte,
      ih.1,ih.2,pow_succ]
    constructor
    · trivial
    · ring

def listReset : List Bool → List Bool → Bool
  | [], _ => true
  | false::_, _ => true
  | true::_, [] => true
  | true::qs, t::ts => (!t) && listReset qs ts

theorem listReset_append (qs ts : List Bool) (h : qs.length=ts.length) :
    listReset (qs++[true]) (ts++[false]) = listReset qs ts := by
  induction qs generalizing ts with
  | nil =>
    have ht : ts=[] := List.length_eq_zero_iff.mp h.symm
    subst ts
    rfl
  | cons q qs ih =>
    cases ts with
    | nil => simp at h
    | cons t ts =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      cases q <;> simp [listReset,ih ts h]

/-- Exact reset recursion even when the fuel word is all ones. -/
theorem listReset_rotation (q t : Bool) (qs ts : List Bool)
    (h : qs.length=ts.length) :
    listReset (q::qs) (t::ts) = ((!q) ||
      ((!t) && listReset (listRotate (q::qs)) (listRotate (t::ts)))) := by
  cases q <;> cases t <;> simp [listReset,listRotate,listReset_append qs ts h]

end
end E2.FiniteConstruction
