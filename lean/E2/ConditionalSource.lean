import E2.SourceClock
import E2.ConditionalCommutations
import E2.ConditionalTail

namespace E2
noncomputable section
open Companion.Analytic
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 200000

def conditionalRelations (p : CounterProgram) : List (SourcePoly p) :=
  [(1-sv p 18)*sv p 21,pc (sv p 19) (sv p 21),pc (sv p 19) (sv p 18),
   pc (sv p 20) (sv p 21),pc (sv p 20) (sv p 18),pc (sv p 19) (sv p 20),
   conjP (sv p 12) (sv p 19)-(4*sv p 19-3*sv p 21),
   conjP (sv p 12) (sv p 20)-(4*sv p 20-3*sv p 18),
   sv p 22*sv p 18*sv p 22-sv p 18,sv p 22*sv p 21*sv p 22-(sv p 18-sv p 21),
   pc (sv p 22) (conjP (sv p 12) (sv p 19)),pc (sv p 22) (sv p 20)]

theorem source_conditional_relation (p : CounterProgram) (r : SourcePoly p) (hr : r∈conditionalRelations p) :
    r∈sourceRelations p := by
  simp only [sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
  iterate 17 apply Or.inr
  apply Or.inl
  exact hr

/-- False selects the data coordinate (B,Q); true selects the flag coordinate
(C,F). Both translate with the original V and retain the original source state. -/
def conditionalClock {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (flag : Bool) : ClockData d :=
  ⟨sourceAt m (if flag then 20 else 19),sourceAt m (if flag then 18 else 21),sourceAt m 12,sourceAt m 22⟩

theorem conditional_affine_approx {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (flag : Bool) : AffineClockApprox m.state δ (conditionalClock m flag) := by
  cases flag
  · refine ⟨?_,?_,?_,?_,?_,sourceAt_state m 19,sourceAt_state m 21,sourceAt_state m 12⟩
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 19 (by omega)
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 21 (by omega)
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 12 (by omega)
    · have h := m.defects (pc (sv p 19) (sv p 21))
        (source_conditional_relation p _ (by simp [conditionalRelations]))
      simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h
    · have h := m.defects (conjP (sv p 12) (sv p 19)-(4*sv p 19-3*sv p 21))
        (source_conditional_relation p _ (by simp [conditionalRelations]))
      simpa [conditionalClock,sourceAt,conjP,Matrix.smul_mul,Matrix.mul_smul] using h
  · refine ⟨?_,?_,?_,?_,?_,sourceAt_state m 20,sourceAt_state m 18,sourceAt_state m 12⟩
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 20 (by omega)
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 18 (by omega)
    · simpa [sourceDomain,conditionalClock] using sourceAt_domain m 12 (by omega)
    · have h := m.defects (pc (sv p 20) (sv p 18))
        (source_conditional_relation p _ (by simp [conditionalRelations]))
      simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h
    · have h := m.defects (conjP (sv p 12) (sv p 20)-(4*sv p 20-3*sv p 18))
        (source_conditional_relation p _ (by simp [conditionalRelations]))
      simpa [conditionalClock,sourceAt,conjP,Matrix.smul_mul,Matrix.mul_smul] using h

theorem conditional_root_coordinate_commutator {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (f g : Bool) :
    weighted m.state (comm (conditionalClock m f).P (conditionalClock m g).A)≤δ := by
  cases f <;> cases g
  all_goals rw [weighted_comm_symm]
  · have h := m.defects (pc (sv p 19) (sv p 21)) (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h
  · have h := m.defects (pc (sv p 20) (sv p 21)) (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h
  · have h := m.defects (pc (sv p 19) (sv p 18)) (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h
  · have h := m.defects (pc (sv p 20) (sv p 18)) (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [conditionalClock,sourceAt,pc,comm,Companion.Analytic.comm] using h

/-- Item (iii) of Lemma 9.3 before inclusion repair, with a single relative
digit-depth factor and one universal constant for all source programs. -/
theorem source_conditional_pair_commutators : ∃ K : ℝ, 1≤K ∧
    ∀ (p : CounterProgram) (d : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ), 0≤δ →
      ∀ f g : Bool, ∀ i j : ℕ, i≤j →
        weighted m.state (comm (rawDigit (conditionalClock m f) i) (rawDigit (conditionalClock m g) j))≤
          18*K*4^(j-i)*δ+2*i*δ := by
  obtain ⟨C,hC,hrepair⟩ := affine_spectral_repair
  refine ⟨C+1,by linarith,?_⟩
  intro p d δ m hδ f g i j hij
  have hf := conditional_affine_approx m f
  have hg := conditional_affine_approx m g
  obtain ⟨r⟩ := hrepair d m.state δ (conditionalClock m g) hδ hg
  have hσ : hs (comm (conditionalClock m f).P m.state.xi)≤δ := by
    cases f <;> exact sourceAt_state m _
  have h := affine_translated_digit_commutator m.state δ (C+1) (conditionalClock m g) hδ (by linarith) hg
    (r.increase (by linarith) hδ) (conditionalClock m f).P (projection_norm_le hf.2.1)
    (conditional_root_coordinate_commutator m f g) hσ i j hij
  exact h

theorem source_conditional_flips : ∃ K : ℝ, 1≤K ∧
    ∀ (p : CounterProgram) (d : ℕ) (δ : ℝ) (m : Model (sourcePresentation p) d δ), 0≤δ →
      (∀ i j : ℕ, i≤j →
        weighted m.state (comm (translate (sourceAt m 12) (sourceAt m 22) i)
          (translate (sourceAt m 12) (sourceAt m 18) j))≤18*K*4^(j-i)*δ+2*i*δ) ∧
      (∀ i j : ℕ, i<j →
        weighted m.state (comm (translate (sourceAt m 12) (sourceAt m 22) i)
          (translate (sourceAt m 12) (sourceAt m 21) j))≤38*K*4^(j-i-1)*δ+2*i*δ) := by
  obtain ⟨C,hC,hrepair⟩ := affine_spectral_repair
  refine ⟨C+1,by linarith,?_⟩
  intro p d δ m hδ
  have hnY : ‖sourceAt m 22‖≤1 :=
    (unitary_norm m.positive_dimension (reflection_unitary _ (by
      simpa [sourceDomain] using sourceAt_domain m 22 (by omega)))).le
  have hYflag : weighted m.state (comm (sourceAt m 22) (sourceAt m 20))≤δ := by
    have h := m.defects (pc (sv p 22) (sv p 20)) (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [pc,sourceAt,comm,Companion.Analytic.comm] using h
  have hYtail : weighted m.state (comm (sourceAt m 22)
      (sourceAt m 12*sourceAt m 19*(sourceAt m 12).conjTranspose))≤δ := by
    have h := m.defects (pc (sv p 22) (conjP (sv p 12) (sv p 19)))
      (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [pc,conjP,sourceAt,comm,Companion.Analytic.comm] using h
  constructor
  · intro i j hij
    have hc := conditional_affine_approx m true
    obtain ⟨r⟩ := hrepair d m.state δ (conditionalClock m true) hδ hc
    have h := affine_translated_digit_commutator m.state δ (C+1) (conditionalClock m true) hδ (by linarith)
      hc (r.increase (by linarith) hδ) (sourceAt m 22) hnY hYflag (sourceAt_state m 22) i j hij
    simpa [conditionalClock,rawDigit] using h
  · intro i j hij
    have hc := conditional_affine_approx m false
    obtain ⟨r⟩ := hrepair d m.state δ (conditionalClock m false) hδ hc
    have h := affine_translated_tail_commutator m.state δ (C+1) (conditionalClock m false) hδ (by linarith)
      hc (r.increase (by linarith) hδ) (sourceAt m 22) hnY (sourceAt_state m 22) hYtail i j hij
    simpa [conditionalClock,rawDigit] using h

theorem source_conditional_own_flip {p : CounterProgram} {d : ℕ} {δ : ℝ}
    (m : Model (sourcePresentation p) d δ) (hδ : 0≤δ) (i : ℕ) :
    let V := sourceAt m 12
    let Y := translate V (sourceAt m 22) i
    let F := translate V (sourceAt m 18) i
    let Q := translate V (sourceAt m 21) i
    weighted m.state (Y*F*Y-F)≤(2*(i:ℝ)+1)*δ ∧
    weighted m.state (Y*Q*Y-(F-Q))≤(3*(i:ℝ)+1)*δ := by
  let V := sourceAt m 12
  let Y := sourceAt m 22
  let F := sourceAt m 18
  let Q := sourceAt m 21
  have hV : Domain.unitary.Holds V := by simpa [V,sourceDomain] using sourceAt_domain m 12 (by omega)
  have hY : Domain.reflection.Holds Y := by simpa [Y,sourceDomain] using sourceAt_domain m 22 (by omega)
  have hF : Domain.projection.Holds F := by simpa [F,sourceDomain] using sourceAt_domain m 18 (by omega)
  have hQ : Domain.projection.Holds Q := by simpa [Q,sourceDomain] using sourceAt_domain m 21 (by omega)
  have hnY : ‖Y‖≤1 := (unitary_norm m.positive_dimension (reflection_unitary Y hY)).le
  have hnF := projection_norm_le hF
  have hnQ := projection_norm_le hQ
  have hnYP (P : Mat d) (hnP : ‖P‖≤1) : ‖Y*P*Y‖≤1 := by
    calc
      _≤‖Y*P‖*‖Y‖ := norm_mul_le _ _
      _≤(‖Y‖*‖P‖)*‖Y‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _≤(1*1)*1 := by gcongr
      _=1 := by norm_num
  have hnE : ‖Y*F*Y-F‖≤2 := (norm_sub_le _ _).trans (by linarith [hnYP F hnF])
  have hnD : ‖Y*Q*Y-(F-Q)‖≤3 := (norm_sub_le _ _).trans
    (by linarith [hnYP Q hnQ,norm_sub_le F Q])
  have hE : weighted m.state (Y*F*Y-F)≤δ := by
    have h := m.defects (sv p 22*sv p 18*sv p 22-sv p 18)
      (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [Y,F,sourceAt] using h
  have hD : weighted m.state (Y*Q*Y-(F-Q))≤δ := by
    have h := m.defects (sv p 22*sv p 21*sv p 22-(sv p 18-sv p 21))
      (source_conditional_relation p _ (by simp [conditionalRelations]))
    simpa [Y,F,Q,sourceAt] using h
  have htE := translate_weighted m.state V (Y*F*Y-F) hV δ hδ (sourceAt_state m 12) i
  have htD := translate_weighted m.state V (Y*Q*Y-(F-Q)) hV δ hδ (sourceAt_state m 12) i
  have hmE := mul_le_mul_of_nonneg_right hnE (mul_nonneg (Nat.cast_nonneg i) hδ)
  have hmD := mul_le_mul_of_nonneg_right hnD (mul_nonneg (Nat.cast_nonneg i) hδ)
  simp only [translate_sub,translate_mul V _ _ hV i] at htE htD
  constructor
  · nlinarith only [htE,hE,hmE]
  · nlinarith only [htD,hD,hmD]

end
end E2
