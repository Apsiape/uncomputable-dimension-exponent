import E2.RealArithmetic

namespace E2.RealArithmetic
noncomputable section

def orderedFreeVars (s : OrderedRingSentence) : List ℕ := freeVars (s.flatten.map Prod.snd)

/-- Full disjunctive-normal-form Tarski semantics is finite existential
quantification over real variables. The infinite ambient index type introduces
no infinitary formula or additional strength into the published hypothesis. -/
theorem ordered_truth_finite (s : OrderedRingSentence) : OrderedRingTruth s ↔
    ∃ v : {i : ℕ // i ∈ orderedFreeVars s} → ℝ,
      ∃ clause ∈ s, ∀ a ∈ clause,
        literalHolds (fun i => if h : i ∈ orderedFreeVars s then v ⟨i,h⟩ else 0) a := by
  classical
  constructor
  · rintro ⟨v,cl,hcl,hv⟩
    refine ⟨fun i => v i,cl,hcl,?_⟩
    intro a ha
    have he : eval (fun i => if h : i ∈ orderedFreeVars s then v i else 0) a.2.2 = eval v a.2.2 := by
      apply eval_congr
      intro m hm i hi
      have hvar : i ∈ orderedFreeVars s := by
        simp only [orderedFreeVars,freeVars,List.mem_flatMap,List.mem_map,List.mem_flatten,List.mem_filterMap]
        exact ⟨a.2,⟨a,⟨cl,hcl,ha⟩,rfl⟩,m,hm,Sum.inr i,hi,rfl⟩
      simp [hvar]
    simpa only [literalHolds,holds,he] using hv a ha
  · rintro ⟨v,cl,hcl,hv⟩
    exact ⟨_,cl,hcl,hv⟩

end
end E2.RealArithmetic
