import E2.SourceJoint

namespace E2
noncomputable section

theorem ExactSlot.ternary_fields {d : ℕ} (x : ExactSlot d) (ht : x.ternary=true) :
    x.measurement.outcomes=3 ∧
    x.measurement.projection (x.measurement.index 0)=1-x.flag ∧
    x.measurement.projection (x.measurement.index 1)=x.flag-x.datum ∧
    x.measurement.projection (x.measurement.index 2)=x.datum := by
  rcases x with ⟨⟨F,R,U,hF,hR,hU,t,hbin⟩,hFR⟩
  cases t <;> simp_all [ExactSlot.measurement,slotMeasurement,conditionalMeasurement,Measurement.index]

theorem ExactSlot.binary_fields {d : ℕ} (x : ExactSlot d) (ht : x.ternary=false) :
    x.measurement.outcomes=2 ∧
    x.measurement.projection (x.measurement.index 0)=1-x.datum ∧
    x.measurement.projection (x.measurement.index 1)=x.datum := by
  rcases x with ⟨⟨F,R,U,hF,hR,hU,t,hbin⟩,hFR⟩
  cases t <;> simp_all [ExactSlot.measurement,slotMeasurement,binaryMeasurement,Measurement.index]

theorem TriangularRelations.mono {d n : ℕ} {s : State d} {η β : ℝ}
    {p : Fin n → Measurement d} {u : Fin n → Mat d}
    (h : TriangularRelations s η p u) (hle : η ≤ β) : TriangularRelations s β p u := by
  rcases h with ⟨hu,hs,hpair,hσ,hown,hlater⟩
  exact ⟨hu,fun i a => (hs i a).trans hle,fun i j hij a b => (hpair i j hij a b).trans hle,
    fun i => (hσ i).trans hle,fun i a => (hown i a).trans hle,fun i j hij a => (hlater i j hij a).trans hle⟩

theorem joint_scale_conversion (K δ : ℝ) (M : ℕ) (hK : 1 ≤ K) (hδ : 0 ≤ δ) :
    212*rawClockScale K M δ ≤ (256*K)*((M:ℝ)+1)^6*4^M*δ := by
  have hbase : (1:ℝ) ≤ (M:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) M; linarith
  have hp : ((M:ℝ)+1)^3 ≤ ((M:ℝ)+1)^6 := pow_le_pow_right₀ hbase (by decide)
  unfold rawClockScale
  calc
    _ = (212*K)*((M:ℝ)+1)^3*4^M*δ := by ring
    _ ≤ _ := by gcongr <;> first | assumption | norm_num

end
end E2
