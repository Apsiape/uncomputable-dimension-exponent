import E2.ExactSourceDefs
import E2.ExactClockModel
import E2.SourceClock

namespace E2.Poly
noncomputable section
variable {A ι κ : Type*} [CStarAlgebra A]

def substitute (f : ι → Poly κ) : Poly ι → Poly κ
  | .const q => .const q
  | .var i => f i
  | .add p q => .add (substitute f p) (substitute f q)
  | .mul p q => .mul (substitute f p) (substitute f q)
  | .adj p => .adj (substitute f p)

theorem evalC_substitute (f : ι → Poly κ) (x : κ → A) (p : Poly ι) :
    (substitute f p).evalC x=p.evalC (fun i => (f i).evalC x) := by
  induction p with
  | const q => rfl
  | var i => rfl
  | add p q hp hq => simp only [substitute,evalC,hp,hq]
  | mul p q hp hq => simp only [substitute,evalC,hp,hq]
  | adj p hp => simp only [substitute,evalC,hp]

end
end E2.Poly

namespace E2.ExactForcing
noncomputable section
variable {A : Type*} [CStarAlgebra A]

theorem sourceValue_domain {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (i : ℕ) (hi : i<23) :
    (sourceDomain p ⟨i,by unfold sourceSize; omega⟩).HoldsC (sourceValue m i) := by
  have h := m.domains ⟨i%sourceSize p,Nat.mod_lt _ (by unfold sourceSize; omega)⟩
  simpa only [sourcePresentation,sourceValue,Nat.mod_eq_of_lt (show i<sourceSize p by unfold sourceSize; omega)] using h

/-- Each of the three source clocks is an actual frozen exact clock model. -/
def sourceClockModel {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (c : Fin 3) :
    ExactModel clockPresentation A where
  state := m.state
  value i := sourceValue m (4*c.val+i.val)
  domains i := by
    have h := sourceValue_domain m (4*c.val+i.val) (by omega)
    fin_cases c <;> fin_cases i <;> simpa [sourceDomain,clockPresentation] using h
  equations r hr := by
    let f : Fin 4 → SourcePoly p := fun i => sv p (4*c.val+i.val)
    have hmap : (clockRelations (.var 0) (.var 1) (.var 2) (.var 3)).map (Poly.substitute f)=
        clockRelations (sv p (4*c.val)) (sv p (4*c.val+1)) (sv p (4*c.val+2)) (sv p (4*c.val+3)) := rfl
    have hmem : Poly.substitute f r ∈ (clockRelations (.var 0) (.var 1) (.var 2) (.var 3)).map (Poly.substitute f) :=
      List.mem_map.mpr ⟨r,hr,rfl⟩
    rw [hmap] at hmem
    have h := m.equations (Poly.substitute f r) (source_clock_relation c _ hmem)
    rw [Poly.evalC_substitute] at h
    exact h

end
end E2.ExactForcing
