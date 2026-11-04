import E2.ExactModelDefs

namespace E2
noncomputable section
variable {A : Type*} [CStarAlgebra A]

def sourceValue {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (n : ℕ) : A :=
  m.value ⟨n % sourceSize p, Nat.mod_lt _ (by unfold sourceSize; omega)⟩
def addressCylinder {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (e : ℕ) : A :=
  let v := sourceValue m
  let e00 := (1-v 1)*(1-ctranslate (v 2) (v 1) 1)
  let e1 := v 1*(1-ctranslate (v 2) (v 1) 1)
  ((List.range e).map (fun j => ctranslate (v 2) e00 (2*j))).prod * ctranslate (v 2) e1 (2*e)
def fuelCylinder {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) : A :=
  let v := sourceValue m
  ((List.range k).map (fun j => ctranslate (v 6) (v 5) j)).prod * (1-ctranslate (v 6) (v 5) k)
def timeZeroCylinder {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (k : ℕ) : A :=
  let v := sourceValue m
  ((List.range k).map (fun j => 1-ctranslate (v 10) (v 9) j)).prod

end
end E2
