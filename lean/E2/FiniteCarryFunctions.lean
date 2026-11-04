import E2.FiniteBitClock

namespace E2.FiniteConstruction
noncomputable section

def boolValue (b : Bool) : ℝ := if b then 1 else 0

def listCoordinate : List Bool → ℝ
  | [] => 0
  | b::bs => (3/4:ℝ)*boolValue b + (1/4:ℝ)*listCoordinate bs

def listCarry : List Bool → ℝ
  | [] => 0
  | false::_ => 1
  | true::bs => (1/4:ℝ)*listCarry bs

def listIncrement : List Bool → List Bool
  | [] => []
  | false::bs => true::bs
  | true::bs => false::listIncrement bs

def listRotate {α : Type*} : List α → List α
  | [] => []
  | a::as => as ++ [a]

theorem listCarry_bounds (bs : List Bool) : 0 ≤ listCarry bs ∧ listCarry bs ≤ 1 := by
  induction bs with
  | nil => simp [listCarry]
  | cons b bs ih => cases b <;> simp only [listCarry] <;> constructor <;> nlinarith [ih.1,ih.2]

theorem listCarry_append_true (bs : List Bool) : listCarry (bs++[true]) = listCarry bs := by
  induction bs with
  | nil => simp [listCarry]
  | cons b bs ih => cases b <;> simp [listCarry,ih]

/-- Exact carry recursion, including the all-ones word. -/
theorem listCarry_rotation (b : Bool) (bs : List Bool) :
    listCarry (b::bs) = (1-boolValue b) +
      (1/4:ℝ)*boolValue b*listCarry (listRotate (b::bs)) := by
  cases b <;> simp [boolValue,listCarry,listRotate,listCarry_append_true]

/-- The only carry-step residual is precisely 4^(-N) at all ones. -/
theorem listIncrement_coordinate (bs : List Bool) :
    listCoordinate (listIncrement bs)-listCoordinate bs+1-(7/4:ℝ)*listCarry bs =
      if bs.all id then (1/4:ℝ)^bs.length else 0 := by
  induction bs with
  | nil => norm_num [listCoordinate,listIncrement,listCarry]
  | cons b bs ih =>
    cases b
    · norm_num [listCoordinate,listIncrement,listCarry,boolValue]
    · simp only [listIncrement,listCoordinate,listCarry,List.length_cons,pow_succ]
      simp only [boolValue,Bool.false_eq_true,↓reduceIte,
        List.all_cons,id_eq,Bool.true_and]
      split_ifs at ih ⊢ <;> nlinarith

theorem listCoordinate_bounds (bs : List Bool) :
    0 ≤ listCoordinate bs ∧ listCoordinate bs ≤ 1-(1/4:ℝ)^bs.length := by
  induction bs with
  | nil => simp [listCoordinate]
  | cons b bs ih =>
    cases b <;> simp only [listCoordinate,boolValue,Bool.false_eq_true,
      ↓reduceIte,List.length_cons,pow_succ]
    all_goals constructor <;> nlinarith [ih.1,ih.2]

theorem listCoordinate_all_ones (bs : List Bool) (h : bs.all id = true) :
    listCoordinate bs = 1-(1/4:ℝ)^bs.length := by
  induction bs with
  | nil => simp [listCoordinate]
  | cons b bs ih =>
    cases b
    · simp at h
    · simp only [List.all_cons,Bool.true_and] at h
      simp only [listCoordinate,boolValue,↓reduceIte,List.length_cons,pow_succ,ih h]
      ring

theorem listIncrement_length (bs : List Bool) : (listIncrement bs).length=bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [listIncrement,ih]

end
end E2.FiniteConstruction
