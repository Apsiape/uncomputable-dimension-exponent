import E2.CompilerUpperActualTables

namespace E2.CompilerUpper
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open E2.CompilerNetwork E2.CompilerDomains E2.CompilerBlocks
variable {V : Type*} [Fintype V] {d : ℕ}

/-- Exact local marginals for each of the six original parity contexts. -/
theorem six_table_measurements (x : V → Mat d)
    (hx : ∀ v, Domain.reflection.Holds (x v)) (a b c : V) (port : Fin 7 → V)
    (h : SixData (x a) (x b) (x c) (x ∘ port)) :
    ∀ t ∈ sixTables a b c port, ∃ A : TableMeasurement t d,
      ∀ v ∈ t.scope, A.marginal v=decodeProjection (x v) := by
  intro t ht
  simp only [sixTables,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.1
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.2.1
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.2.2.1
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.2.2.2.1
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.2.2.2.2.1
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) h.2.2.2.2.2.2

/-- All 31 parity tables of a complete conjugacy gadget, with original ports. -/
theorem conjugacy_table_measurements (x : V → Mat d)
    (hx : ∀ v, Domain.reflection.Holds (x v)) (a b c : V) (port : GadgetWire → V)
    (hg : GeneralData (fun i => x (![a,b,c] i)) (fun j => x (port (.inl j))))
    (hs : ∀ i, SixData (subA (fun j => x (port (.inl j))) i)
      (subB (fun j => x (port (.inl j))) i) (subC (fun j => x (port (.inl j))) i)
      (fun j => x (port (.inr (i,j))))) :
    ∀ t ∈ conjugacyTables a b c port, ∃ A : TableMeasurement t d,
      ∀ v ∈ t.scope, A.marginal v=decodeProjection (x v) := by
  intro t ht
  simp only [conjugacyTables,List.mem_append,List.mem_map,List.mem_flatMap,List.mem_singleton,List.not_mem_nil,or_false] at ht
  rcases ht with (((⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩) | rfl) | ⟨i,hi,ht⟩) | ht
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) (hg.xyz i)
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) (hg.xfw i)
  · exact parity_measurement _ _ _ x (hx _) (hx _) (hx _) hg.gyz
  · apply six_table_measurements x hx _ _ _ _ (by
      fin_cases i
      · exact hs 0
      · exact hs 1
      · exact hs 2) t ht
  · exact six_table_measurements x hx _ _ _ _ (hs 3) t ht

/-- Concrete gadget inputs and disjoint auxiliaries satisfy every parity table. -/
theorem actual_gadget_measurements {ι : Type*} [Fintype ι]
    (P : Presentation ι) (s : ι × Fin 2 → Mat d) (aux)
    (hx : ∀ w, Domain.reflection.Holds (wireValue P s aux w))
    (hg : ∀ k, GeneralData (fun i => wireValue P s aux (gadgetInputs P k i))
      (fun j => aux k (.inl j)))
    (hs : ∀ k i, SixData (subA (fun j => aux k (.inl j)) i)
      (subB (fun j => aux k (.inl j)) i) (subC (fun j => aux k (.inl j)) i)
      (fun j => aux k (.inr (i,j)))) (k : GadgetKey P) :
    ∀ t ∈ conjugacyTables (gadgetInputs P k 0) (gadgetInputs P k 1) (gadgetInputs P k 2)
      (auxiliary P k.1 k.2), ∃ A : TableMeasurement t (2*(2*(registerSize P*d))),
      ∀ v ∈ t.scope, A.marginal v=decodeProjection (wireValue P s aux v) := by
  apply conjugacy_table_measurements (wireValue P s aux) hx
  · have he : (fun i => wireValue P s aux (![gadgetInputs P k 0,gadgetInputs P k 1,gadgetInputs P k 2] i))=
        (fun i => wireValue P s aux (gadgetInputs P k i)) := by
      funext i; fin_cases i <;> rfl
    simpa only [wireValue_auxiliary,he] using hg k
  · simpa only [wireValue_auxiliary] using hs k

end
end E2.CompilerUpper

