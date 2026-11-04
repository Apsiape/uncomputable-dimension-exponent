import E2.CompilerUpperParityTables

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks E2.FiniteConstruction
variable {V : Type*} [Fintype V] {d : ℕ}
local instance : DecidableEq V := Classical.decEq V

/-- Exact table marginals imply every nonnegative uniform error bound. -/
theorem exact_measurement_bound (t : Table V) (x : V → Mat d) (s : State d) (ε : ℝ) (hε : 0≤ε)
    (h : ∃ A : TableMeasurement t d, ∀ v ∈ t.scope, A.marginal v=decodeProjection (x v)) :
    ∃ A : TableMeasurement t d, ∀ v ∈ t.scope, weighted s (A.marginal v-decodeProjection (x v))≤ε := by
  obtain ⟨A,hA⟩ := h
  exact ⟨A,fun v hv => by simpa [hA v hv] using hε⟩

/-- Exact free-table marginals for a finite family specified by ports. -/
theorem free_image_measurement {n : ℕ} (port : Fin n → V) (x : V → Mat d)
    (hx : ∀ v, Domain.reflection.Holds (x v)) (hc : ∀ i j, Commute (x (port i)) (x (port j))) :
    ∃ A : TableMeasurement (free (Finset.univ.image port)) d,
      ∀ v ∈ (free (Finset.univ.image port)).scope, A.marginal v=decodeProjection (x v) := by
  apply free_measurement
  · exact fun v _ => hx v
  · intro v hv w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    exact hc i j

theorem free_pair_measurement (a b : V) (x : V → Mat d)
    (hx : ∀ v, Domain.reflection.Holds (x v)) (hc : Commute (x a) (x b)) :
    ∃ A : TableMeasurement (free {a,b}) d,
      ∀ v ∈ (free {a,b}).scope, A.marginal v=decodeProjection (x v) := by
  apply free_measurement
  · exact fun v _ => hx v
  · intro v hv w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _

/-- Exhaustive eliminator for the unchanged concrete relation-table list. -/
theorem relation_tables_cases {ι : Type*} [Fintype ι] (P : Presentation ι)
    (r : Fin P.relations.length) (Good : Table (Wire P) → Prop)
    (hand : Good (andTable (E P r) (Finset.univ.image (X P r))))
    (hortho : Good (orthogonal (E P r) (F P r)))
    (hX : Good (free (Finset.univ.image (X P r))))
    (hZ : Good (free (Finset.univ.image (Z P r))))
    (hSX : ∀ s i, Good (free {source P s,X P r i}))
    (hSZ : ∀ s i, Good (free {source P s,Z P r i}))
    (hXZ : ∀ i j, i≠j → Good (free {X P r i,Z P r j}))
    (hneg : ∀ j, Good (functional {Z P r j} (negZ P r j) (by simp [negZ,Z,localWire])
      (fun a => !(a (Z P r j))) (by intro a b h; rw [h _ (by simp)])))
    (hcontrol : ∀ j, Good (controlTable P r j))
    (hgadget : ∀ k, ∀ t ∈ conjugacyTables (gadgetInputs P ⟨r,k⟩ 0) (gadgetInputs P ⟨r,k⟩ 1)
      (gadgetInputs P ⟨r,k⟩ 2) (auxiliary P r k), Good t) :
    ∀ t ∈ relationTables P r, Good t := by
  intro t ht
  simp only [relationTables,List.mem_append,List.mem_cons,List.mem_singleton,List.mem_flatMap,List.mem_map,List.not_mem_nil,or_false] at ht
  rcases ht with ((((((ht | ht) | ht) | ht) | ht) | ht) | ht)
  · rcases ht with rfl | rfl
    · exact hand
    · exact hortho
  · rcases ht with rfl | rfl
    · exact hX
    · exact hZ
  · obtain ⟨⟨s,i⟩,_,ht⟩ := ht
    rcases ht with rfl | rfl
    · exact hSX s i
    · exact hSZ s i
  · obtain ⟨⟨i,j⟩,_,ht⟩ := ht
    split_ifs at ht with h
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst t
      exact hXZ i j h
  · obtain ⟨j,_,ht⟩ := ht
    rcases ht with ht | ht
    · rcases ht with rfl
      exact hneg j
    · have h := hgadget (Fin.castAdd (steps P r) j) t
      simp [gadgetInputs] at h
      have hk : Fin.castAdd (steps P r) j=(⟨j.val,by have := j.isLt; omega⟩ : Fin (q P r+steps P r)) := by
        apply Fin.ext; rfl
      rw [hk] at h
      exact h ht
  · obtain ⟨j,_,rfl⟩ := ht
    exact hcontrol j
  · obtain ⟨j,_,ht⟩ := ht
    have h := hgadget (Fin.natAdd (q P r) j) t
    simp [gadgetInputs,previousWire] at h
    have hk : Fin.natAdd (q P r) j=(⟨q P r+j.val,by have := j.isLt; omega⟩ : Fin (q P r+steps P r)) := by
      apply Fin.ext; rfl
    rw [hk] at h
    exact h ht

/-- Uniform local bounds for every table in the actual relation network. -/
theorem actual_relation_table_bounds {ι : Type*} [Fintype ι]
    (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (hx : ∀ w, Domain.reflection.Holds (wireValue P s aux w))
    (hg : ∀ k, GeneralData (fun i => wireValue P s aux (gadgetInputs P k i))
      (fun j => aux k (.inl j)))
    (hs : ∀ k i, SixData (subA (fun j => aux k (.inl j)) i)
      (subB (fun j => aux k (.inl j)) i) (subC (fun j => aux k (.inl j)) i)
      (fun j => aux k (.inr (i,j))))
    (state : State (2*(2*(registerSize P*d)))) (ε : ℝ) (hε : 0≤ε)
    (R : Fin P.relations.length → Mat (2*(2*(registerSize P*d))))
    (hR : ∀ r, Domain.projection.Holds (R r) ∧
      decodeProjection (wireValue P s aux (E P r))*R r=0 ∧
      R r*decodeProjection (wireValue P s aux (E P r))=0 ∧
      weighted state (R r-decodeProjection (wireValue P s aux (F P r)))≤ε)
    (r : Fin P.relations.length) :
    ∀ t ∈ relationTables P r, ∃ A : TableMeasurement t (2*(2*(registerSize P*d))),
      ∀ v ∈ t.scope, weighted state (A.marginal v-decodeProjection (wireValue P s aux v))≤ε := by
  classical
  apply relation_tables_cases
  · exact exact_measurement_bound _ _ state ε hε (actual_and_measurement P s aux r)
  · obtain ⟨A,_,hE,hF⟩ := actual_orthogonal_measurement P s aux r (R r)
      (decode_projection _ (hx _)) (hR r).1 (hR r).2.1 (hR r).2.2.1
    refine ⟨A,?_⟩
    intro v hv
    simp only [orthogonal,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simpa [hE] using hε
    · rw [hF]; exact (hR r).2.2.2
  · apply exact_measurement_bound _ _ state ε hε
    apply free_image_measurement _ _ hx
    intro i j
    exact duplicate_commute _ _ (duplicate_commute _ _ (baseXX P r i j))
  · apply exact_measurement_bound _ _ state ε hε
    apply free_image_measurement _ _ hx
    intro i j
    exact duplicate_commute _ _ (duplicate_commute _ _ (baseZZ P r i j))
  · intro k i
    apply exact_measurement_bound _ _ state ε hε
    apply free_pair_measurement _ _ _ hx
    exact duplicate_commute _ _ (duplicate_commute _ _ (baseSourceX P s k r i))
  · intro k i
    apply exact_measurement_bound _ _ state ε hε
    apply free_pair_measurement _ _ _ hx
    exact duplicate_commute _ _ (duplicate_commute _ _ (baseSourceZ P s k r i))
  · intro i j hij
    apply exact_measurement_bound _ _ state ε hε
    apply free_pair_measurement _ _ _ hx
    exact duplicate_commute _ _ (duplicate_commute _ _ (baseXZ P r i j hij))
  · intro j
    exact exact_measurement_bound _ _ state ε hε (actual_negation_measurement P s aux hx r j)
  · intro j
    exact exact_measurement_bound _ _ state ε hε (actual_control_measurement P s aux hx r j)
  · intro k t ht
    exact exact_measurement_bound _ _ state ε hε (actual_gadget_measurements P s aux hx hg hs ⟨r,k⟩ t ht)

end
end E2.CompilerUpper


