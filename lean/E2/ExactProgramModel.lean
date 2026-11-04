import E2.ExactProgramActions
import E2.ExactGNSModel

namespace E2.ExactForcing
noncomputable section
open scoped BigOperators
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

def sourceWork (p : CounterProgram) : List (SourcePoly p) :=
  (List.finRange p.counters).flatMap (fun i => [sr p i,sz p i,ss p i]) ++
    (List.finRange p.controls).map (sq p)

theorem sr_mem_work (p : CounterProgram) (i : Fin p.counters) : sr p i ∈ sourceWork p := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,by simp⟩

theorem sz_mem_work (p : CounterProgram) (i : Fin p.counters) : sz p i ∈ sourceWork p := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,by simp⟩

theorem ss_mem_work (p : CounterProgram) (i : Fin p.counters) : ss p i ∈ sourceWork p := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,by simp⟩

theorem sq_mem_work (p : CounterProgram) (i : Fin p.controls) : sq p i ∈ sourceWork p := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩

theorem workspace_comm {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (x y : SourcePoly p) (hx : x ∈ sv p 17 :: sourceWork p) (hy : y ∈ sv p 17 :: sourceWork p) :
    Commute (x.evalC m.value) (y.evalC m.value) := by
  apply sub_eq_zero.mp
  have hr : pc x y ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 15 apply Or.inr
    apply Or.inl
    exact commList_mem _ _ _ _ hx hy
  simpa only [pc,Poly.evalC_sub,Poly.evalC_mul] using m.equations _ hr

theorem counter_domain {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (i : Fin p.counters) :
    Domain.positiveContraction.HoldsC ((sr p i).evalC m.value) ∧
    Domain.projection.HoldsC ((sz p i).evalC m.value) ∧
    Domain.positiveContraction.HoldsC ((ss p i).evalC m.value) := by
  have h0 : 23+3*i.val<sourceSize p := by unfold sourceSize; omega
  have h1 : 24+3*i.val<sourceSize p := by unfold sourceSize; omega
  have h2 : 25+3*i.val<sourceSize p := by unfold sourceSize; omega
  have hdom (n : ℕ) (hn : n<sourceSize p) :
      (sourceDomain p ⟨n,hn⟩).HoldsC ((sv p n).evalC m.value) := by
    simpa only [sourcePresentation,sv,Poly.evalC_var,Nat.mod_eq_of_lt hn] using m.domains ⟨n,hn⟩
  have hi := i.isLt
  have hm0 : (23+3*i.val-23)%3=0 := by omega
  have hm1 : (24+3*i.val-23)%3=1 := by omega
  have hm2 : (25+3*i.val-23)%3=2 := by omega
  have hd0 : sourceDomain p ⟨23+3*i.val,h0⟩=Domain.positiveContraction := by
    simp only [sourceDomain,Fin.val_mk,hm0]
    split_ifs <;> first | rfl | omega
  have hd1 : sourceDomain p ⟨24+3*i.val,h1⟩=Domain.projection := by
    simp only [sourceDomain,Fin.val_mk,hm1]
    split_ifs <;> first | rfl | omega
  have hd2 : sourceDomain p ⟨25+3*i.val,h2⟩=Domain.positiveContraction := by
    simp only [sourceDomain,Fin.val_mk,hm2]
    split_ifs <;> first | rfl | omega
  exact ⟨by simpa only [hd0,sr] using hdom _ h0,
    by simpa only [hd1,sz] using hdom _ h1,by simpa only [hd2,ss] using hdom _ h2⟩

theorem source_zero_equation {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (i : Fin p.counters) :
    (sr p i).evalC m.value=(sz p i).evalC m.value+
      (1/2:ℂ) • ((1-(sz p i).evalC m.value)*(ss p i).evalC m.value) := by
  have hr : sr p i-(sz p i+.const (1/2)*(1-sz p i)*ss p i) ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 7 apply Or.inr
    apply Or.inl
    exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
  apply sub_eq_zero.mp
  simpa only [Poly.evalC_sub,Poly.evalC_add,Poly.evalC_mul,Poly.evalC_const,Poly.evalC_one,
    smul_mul_assoc,one_mul,mul_smul_comm,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using m.equations _ hr

theorem model_zero_test {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (f : A →⋆ₐ[ℂ] A) (Q : A) (c : Configuration p)
    (hr : ∀ i, f ((sr p i).evalC m.value)*Q=counterCode (c.counter i) • Q) :
    ∀ i, f ((sz p i).evalC m.value)*Q=if c.counter i=0 then Q else 0 := by
  intro i
  have hd := counter_domain m i
  have hsd := ExactTrace.domain_map f Domain.positiveContraction _ hd.2.2
  have hzd := ExactTrace.domain_map f Domain.projection _ hd.2.1
  apply zero_test _ _ _ Q hzd.2
  · simpa only [map_mul] using congrArg f (workspace_comm m _ _ (List.mem_cons_of_mem _ (sz_mem_work p i))
      (List.mem_cons_of_mem _ (ss_mem_work p i))).eq
  · exact contraction_norm _ hsd.1 hsd.2
  · simpa only [map_add,map_smul,map_mul,map_sub,map_one] using congrArg f (source_zero_equation m i)
  · exact hr i

def timeStep {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) : A →⋆ₐ[ℂ] A :=
  shiftHom (star (sourceValue m 13))
    (by simpa only [star_star] using (show Domain.unitary.HoldsC (sourceValue m 13) from
      by simpa [sourceDomain] using sourceValue_domain m 13 (by omega)).symm) 1

theorem timeStep_apply {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (x : A) :
    timeStep m x=star (sourceValue m 13)*x*sourceValue m 13 := by
  change ctranslate (star (sourceValue m 13)) x 1=_
  simp only [ctranslate,pow_one,star_star]

theorem source_update {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (w ini nxt : SourcePoly p)
    (hr : conjP (sv p 13).adj w -
      (conjP (sv p 13).adj (sv p 17)*ini+(1-conjP (sv p 13).adj (sv p 17))*nxt)
        ∈ (sourcePresentation p).relations) :
    timeStep m (w.evalC m.value)=timeStep m (sourceValue m 17)*ini.evalC m.value+
      (1-timeStep m (sourceValue m 17))*nxt.evalC m.value := by
  apply sub_eq_zero.mp
  simpa only [conjP,Poly.evalC_sub,Poly.evalC_add,Poly.evalC_mul,Poly.evalC_adj,Poly.evalC_one,
    sv,Poly.evalC_var,sourceValue,timeStep_apply,star_star] using m.equations _ hr

theorem counter_updates {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (i : Fin p.counters) :
    sourceValue m 17*(sr p i).evalC m.value=sourceValue m 17*(initialCounter p i).evalC m.value ∧
    timeStep m ((sr p i).evalC m.value)=
      timeStep m (sourceValue m 17)*(initialCounter p i).evalC m.value+
        (1-timeStep m (sourceValue m 17))*(nextCounter p i).evalC m.value := by
  have hm (r : SourcePoly p) (hr : r ∈
      [sv p 17*sr p i-sv p 17*initialCounter p i,
       conjP (sv p 13).adj (sr p i)-
        (conjP (sv p 13).adj (sv p 17)*initialCounter p i+
          (1-conjP (sv p 13).adj (sv p 17))*nextCounter p i)]) :
      r ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 10 apply Or.inr
    apply Or.inl
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hr⟩
  constructor
  · apply sub_eq_zero.mp
    simpa only [Poly.evalC_sub,Poly.evalC_mul,sv,Poly.evalC_var,sourceValue] using m.equations _ (hm (sv p 17*sr p i-sv p 17*initialCounter p i) (by simp))
  · exact source_update m _ _ _ (hm _ (by simp))

theorem control_updates {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) (i : Fin p.controls) :
    sourceValue m 17*(sq p i).evalC m.value=sourceValue m 17*(initialControl p i).evalC m.value ∧
    timeStep m ((sq p i).evalC m.value)=
      timeStep m (sourceValue m 17)*(initialControl p i).evalC m.value+
        (1-timeStep m (sourceValue m 17))*(nextControl p i).evalC m.value := by
  have hm (r : SourcePoly p) (hr : r ∈
      [sv p 17*sq p i-sv p 17*initialControl p i,
       conjP (sv p 13).adj (sq p i)-
        (conjP (sv p 13).adj (sv p 17)*initialControl p i+
          (1-conjP (sv p 13).adj (sv p 17))*nextControl p i)]) :
      r ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 11 apply Or.inr
    apply Or.inl
    exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hr⟩
  constructor
  · apply sub_eq_zero.mp
    simpa only [Poly.evalC_sub,Poly.evalC_mul,sv,Poly.evalC_var,sourceValue] using m.equations _ (hm (sv p 17*sq p i-sv p 17*initialControl p i) (by simp))
  · exact source_update m _ _ _ (hm _ (by simp))

end
end E2.ExactForcing
