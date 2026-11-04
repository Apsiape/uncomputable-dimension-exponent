import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem decodedR_bounds (bs : List Bool) : 0 ≤ decodedR bs ∧ decodedR bs ≤ 1 := by
  unfold decodedR
  cases h : binaryDecode bs
  · norm_num
  · exact counterCoordinate_bounds _

theorem historyR_bounds (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) :
    0 ≤ historyR p bs qs ts i ∧ historyR p bs qs ts i ≤ 1 := by
  unfold historyR
  split_ifs
  · norm_num
  · exact counterCoordinate_bounds _

theorem historyS_bounds (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) :
    0 ≤ historyS p bs qs ts i ∧ historyS p bs qs ts i ≤ 1 := by
  unfold historyS
  split_ifs
  · norm_num
  · exact counterWitness_bounds _

theorem history_zero_test (p : CounterProgram) (bs qs ts : List Bool) (i : Fin p.counters) :
    historyR p bs qs ts i = historyZ p bs qs ts i +
      (1/2:ℝ)*(1-historyZ p bs qs ts i)*historyS p bs qs ts i := by
  unfold historyR historyZ historyS
  split_ifs
  · norm_num
  · exact counter_zero_test _

theorem sourcePerm_basis (N k : ℕ) (s : Equiv.Perm (SourceBasis N k)) (i : Fin (2^(3*N+k))) :
    sourceBasisEquiv N k (sourcePerm N k s i)=s (sourceBasisEquiv N k i) := by
  simp [sourcePerm]

theorem conjugate_involutive {α : Type*} (d u : Equiv.Perm α) (hu : Function.Involutive u) :
    Function.Involutive (d.symm.trans (u.trans d)) := by
  intro a
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  rw [hu (d.symm a),d.apply_symm_apply]

theorem prod_involutive {α β : Type*} (s : Equiv.Perm α) (t : Equiv.Perm β)
    (hs : Function.Involutive s) (ht : Function.Involutive t) : Function.Involutive (s.prodCongr t) := by
  rintro ⟨a,b⟩
  exact congrArg₂ Prod.mk (hs a) (ht b)

theorem flipFirstWord_involutive (N : ℕ) : Function.Involutive (flipFirstWord N) := by
  intro b
  exact (flipFirstWord N).left_inv b

theorem addressFlip_involutive (p : CounterProgram) (N k : ℕ) :
    Function.Involutive (addressFlip p N k) :=
  conjugate_involutive _ _ (prod_involutive _ _ (flipFirstWord_involutive N) (fun _ => rfl))

theorem sourcePerm_involutive (N k : ℕ) (s : Equiv.Perm (SourceBasis N k))
    (hs : Function.Involutive s) : Function.Involutive (sourcePerm N k s) := by
  intro i
  apply (sourceBasisEquiv N k).injective
  rw [sourcePerm_basis,sourcePerm_basis,hs]

theorem reflection_of_involutive {α : Type*} [Fintype α] [DecidableEq α]
    (s : Equiv.Perm α) (hs : Function.Involutive s) :
    (s.permMatrix ℂ).conjTranspose=s.permMatrix ℂ ∧ s.permMatrix ℂ*s.permMatrix ℂ=1 := by
  have hi : s.symm=s := by
    apply Equiv.ext
    intro a
    apply s.injective
    rw [s.apply_symm_apply,hs]
  have hc : (s.permMatrix ℂ).conjTranspose=s.permMatrix ℂ := by
    rw [Matrix.conjTranspose_permMatrix]
    exact congrArg (fun t : Equiv.Perm α => t.permMatrix ℂ) hi
  exact ⟨hc,by simpa only [hc] using (perm_unitary s).1⟩

theorem source_reflection (N k : ℕ) (s : Equiv.Perm (SourceBasis N k))
    (hs : Function.Involutive s) : Domain.reflection.Holds ((sourcePerm N k s).permMatrix ℂ) :=
  reflection_of_involutive _ (sourcePerm_involutive N k s hs)

theorem sourceDiagonal_contraction (N k : ℕ) (a : SourceBasis N k → ℝ)
    (ha : ∀ z, 0 ≤ a z ∧ a z ≤ 1) : Domain.positiveContraction.Holds (sourceDiagonal N k a) :=
  diagonal_positive_contraction _ (fun i => ha _)

theorem sourceDiagonal_projection (N k : ℕ) (a : SourceBasis N k → Bool) :
    Domain.projection.Holds (sourceDiagonal N k (fun z => boolValue (a z))) := by
  simpa only [Domain.Holds,sourceDiagonal,boolValue,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using
    diagonal_projection (fun i => a (sourceBasisEquiv N k i))

theorem sourceCore_domain (p : CounterProgram) (N : ℕ) (n : Fin 23) :
    (sourceDomain p ⟨n.val,by have := n.isLt; unfold sourceSize; omega⟩).Holds (sourceCore p N n.val) := by
  let k := finiteSlots p N
  haveI : NeZero k := ⟨Nat.ne_of_gt (finiteSlots_pos p N)⟩
  fin_cases n <;> norm_num only [sourceDomain,Fin.val_mk] <;>
    simp only [or_false,or_true,false_or,true_or,ite_true,ite_false]
  · apply sourceDiagonal_contraction
    intro z
    have h := listCoordinate_bounds z.1.1.val
    exact ⟨h.1,h.2.trans (sub_le_self 1 (by positivity))⟩
  · exact sourceDiagonal_projection _ _ _
  · exact perm_unitary _
  · apply source_reflection
    exact prod_involutive _ _ (addressFlip_involutive p N k) (fun _ => rfl)
  · apply sourceDiagonal_contraction
    intro z
    have h := listCoordinate_bounds z.2.1.val
    exact ⟨h.1,h.2.trans (sub_le_self 1 (by positivity))⟩
  · exact sourceDiagonal_projection _ _ _
  · exact perm_unitary _
  · apply source_reflection
    exact prod_involutive _ _ (fun _ => rfl)
      (prod_involutive _ _ (flipFirstWord_involutive N) (fun _ => rfl))
  · apply sourceDiagonal_contraction
    intro z
    have h := listCoordinate_bounds z.2.2.val
    exact ⟨h.1,h.2.trans (sub_le_self 1 (by positivity))⟩
  · exact sourceDiagonal_projection _ _ _
  · exact perm_unitary _
  · apply source_reflection
    exact prod_involutive _ _ (fun _ => rfl)
      (prod_involutive _ _ (fun _ => rfl) (flipFirstWord_involutive N))
  · exact perm_unitary _
  · exact perm_unitary _
  · exact sourceDiagonal_contraction _ _ _ (fun z => listCarry_bounds _)
  · exact sourceDiagonal_projection _ _ _
  · exact sourceDiagonal_contraction _ _ _ (fun z => decodedR_bounds _)
  · exact sourceDiagonal_projection _ _ _
  · simpa only [sourceCore,optionalFlag,boolValue] using
      sourceDiagonal_projection N k (fun z => wordMask p N z.1.1)
  · exact sourceDiagonal_contraction _ _ _ (fun z => permutationSeries_bounds _ _ (optionalDigit_bounds _) _)
  · exact sourceDiagonal_contraction _ _ _ (fun z => permutationSeries_bounds _ _ (optionalFlag_bounds _) _)
  · have he : (fun z : SourceBasis N k => optionalDigit (wordMask p N) z.1) =
        (fun z => boolValue (wordMask p N z.1.1 && z.1.2 0)) := by
      funext z
      cases h : wordMask p N z.1.1 <;> simp [optionalDigit,boolValue,bit,h]
    change Domain.projection.Holds (sourceDiagonal N k _)
    rw [he]
    exact sourceDiagonal_projection _ _ _
  · apply source_reflection
    apply prod_involutive _ _ _ (fun _ => rfl)
    intro z
    exact (optionalFlip (wordMask p N)).left_inv z

theorem sourceTuple_domains (p : CounterProgram) (N : ℕ) (j : SourceVar p) :
    ((sourcePresentation p).domain j).Holds (sourceTuple p N j) := by
  change (sourceDomain p j).Holds _
  by_cases hcore : j.val<23
  · have he : j=⟨(⟨j.val,hcore⟩:Fin 23).val,by have := j.isLt; exact this⟩ := rfl
    simpa only [sourceTuple,hcore,↓reduceDIte] using sourceCore_domain p N ⟨j.val,hcore⟩
  · by_cases hc : j.val<23+3*p.counters
    · have hdom : sourceDomain p j =
          if (j.val-23)%3=1 then Domain.projection else Domain.positiveContraction := by
        unfold sourceDomain
        split_ifs <;> first | rfl | omega
      rw [hdom]
      simp only [sourceTuple,hcore,hc,↓reduceDIte]
      let i : Fin p.counters := ⟨(j.val-23)/3,by omega⟩
      by_cases hr : (j.val-23)%3=0
      · simp only [hr,show ¬(0:ℕ)=1 by omega,↓reduceIte]
        exact sourceDiagonal_contraction _ _ _ (fun z => historyR_bounds p _ _ _ i)
      · by_cases hz : (j.val-23)%3=1
        · simp only [hz,↓reduceIte]
          have he : (fun z : SourceBasis N (finiteSlots p N) =>
              historyZ p z.1.1.val z.2.1.val z.2.2.val i) =
              (fun z => boolValue (decide (¬(binaryDecode z.1.1.val=none ∧ i.val=0) ∧
                (historyConfig p z.1.1.val z.2.1.val z.2.2.val).counter i=0))) := by
            funext z
            by_cases hs : binaryDecode z.1.1.val=none ∧ i.val=0 <;>
              simp [historyZ,counterZero,boolValue,hs]
          change Domain.projection.Holds (sourceDiagonal N (finiteSlots p N) _)
          rw [he]
          exact sourceDiagonal_projection _ _ _
        · have ht : (j.val-23)%3=2 := by have := Nat.mod_lt (j.val-23) (by omega : 0<3); omega
          simp only [ht,show ¬(2:ℕ)=1 by omega,↓reduceIte]
          exact sourceDiagonal_contraction _ _ _ (fun z => historyS_bounds p _ _ _ i)
    · have hdom : sourceDomain p j=Domain.projection := by
        unfold sourceDomain
        split_ifs <;> first | rfl | omega
      rw [hdom]
      simp only [sourceTuple,hcore,hc,↓reduceDIte]
      simpa only [boolValue,decide_eq_true_eq] using sourceDiagonal_projection N (finiteSlots p N)
        (fun z => decide ((⟨j.val-(23+3*p.counters),by have := j.isLt; unfold sourceSize at this; omega⟩:Fin p.controls)=
          (historyConfig p z.1.1.val z.2.1.val z.2.2.val).control))
end
end E2.FiniteConstruction