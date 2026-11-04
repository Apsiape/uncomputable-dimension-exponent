import E2.FiniteCarryFunctions

namespace E2.FiniteConstruction
noncomputable section

def listRotateBack {α : Type*} (bs : List α) : List α :=
  match bs.reverse with
  | [] => []
  | b::bs => b::bs.reverse

def listFlipFirst : List Bool → List Bool
  | [] => []
  | b::bs => (!b)::bs

def recursiveIncrement : List Bool → List Bool
  | [] => []
  | false::bs => true::bs
  | true::bs => listFlipFirst (listRotateBack (listIncrement (bs++[true])))

theorem listRotateBack_append {α : Type*} (bs : List α) (b : α) :
    listRotateBack (bs++[b]) = b::bs := by
  simp [listRotateBack]

theorem listIncrement_append_true (bs : List Bool) :
    listIncrement (bs++[true]) =
      listIncrement bs ++ [if bs.all id then false else true] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simp [listIncrement]
    · simpa only [List.cons_append,listIncrement,List.all_cons,id_eq,Bool.true_and] using
        congrArg (List.cons false) ih

/-- Exact boundary formula for the recursive increment: it agrees with the
cyclic increment everywhere except the all-ones input, where its output is
the first-bit flip of the true increment's output. -/
theorem recursiveIncrement_boundary (bs : List Bool) :
    recursiveIncrement bs =
      if bs.all id then listFlipFirst (listIncrement bs) else listIncrement bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases b
    · simp [recursiveIncrement,listIncrement]
    · rw [recursiveIncrement,listIncrement_append_true,listRotateBack_append]
      by_cases h : bs.all id = true <;>
        simp [h,listFlipFirst,listIncrement]

theorem recursiveIncrement_interior (bs : List Bool) (h : bs.all id = false) :
    recursiveIncrement bs = listIncrement bs := by
  simp [recursiveIncrement_boundary,h]

theorem recursiveIncrement_length (bs : List Bool) :
    (recursiveIncrement bs).length=bs.length := by
  rw [recursiveIncrement_boundary]
  split_ifs
  · cases h : listIncrement bs <;> simp [listFlipFirst,←listIncrement_length bs,h]
  · exact listIncrement_length bs

theorem guardedIncrement_weight (bs : List Bool)
    (h : recursiveIncrement bs ≠ listIncrement bs) :
    1-listCoordinate bs=(1/4:ℝ)^bs.length := by
  have hall : bs.all id = true := by
    cases he : bs.all id
    · exact False.elim (h (recursiveIncrement_interior bs he))
    · rfl
  rw [listCoordinate_all_ones bs hall]
  ring

end
end E2.FiniteConstruction
