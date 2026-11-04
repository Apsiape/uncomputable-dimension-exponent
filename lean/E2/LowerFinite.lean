import E2.LowerTransport
import E2.Turn9.LowerStatements

namespace E2
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 200000

/-- The full finite-depth inequality needed by the lower assembly, with no
new input beyond the original count premise and the original JointFamily. -/
theorem joint_count_lower : Turn9.JointCountLower := by
  intro p C K hC hK count d M δ m r hδ he
  have hη : 0≤jointError M δ K := by unfold jointError; positivity
  have hcount := count d (4*M) m.state (jointError M δ K) r.measurement r.unitary
    m.positive_dimension hη r.relations (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using he)
  rw [r.binary_count] at hcount
  have hactive := joint_active_lower m r hδ
  dsimp [Turn9.countPenalty]
  push_cast at hcount ⊢
  nlinarith only [hcount,hactive]

end
end E2

