import E2.CompilerFrontend
import E2.CompilerRealification
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace E2.CompilerDomains
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Every positive contraction has an exact unitary preimage under the
compiler's fixed decoder. No enlargement or approximate square root is used. -/
theorem positive_unitary_lift {d : ℕ} (A : Mat d)
    (hA : Domain.positiveContraction.Holds A) :
    ∃ U : Mat d, Domain.unitary.Holds U ∧ decodePositive U = A := by
  have ha : 0 ≤ A := hA.1.nonneg
  have hb : 0 ≤ 1-A := hA.2.nonneg
  have hna : ‖A‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg A ha).mpr
    (sub_nonneg.mp hb)
  have hnb : ‖1-A‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg (1-A) hb).mpr
    (by simpa using ha)
  let B : Mat d := A-(1-A)
  have hB : IsSelfAdjoint B := (IsSelfAdjoint.of_nonneg ha).sub (IsSelfAdjoint.of_nonneg hb)
  have hnB : ‖B‖ ≤ 1 := (CStarAlgebra.norm_sub_le_max_of_nonneg ha hb).trans
    (max_le hna hnb)
  let b : selfAdjoint (Mat d) := ⟨B,hB⟩
  let u := selfAdjoint.unitarySelfAddISMul b hnB
  refine ⟨u,?_,?_⟩
  · exact ⟨Unitary.coe_star_mul_self u,Unitary.coe_mul_star_self u⟩
  · have hstar : (star u : Mat d) = B-Complex.I • CFC.sqrt (1-B^2) :=
      selfAdjoint.star_coe_unitarySelfAddISMul b hnB
    have hu : (u : Mat d) = B+Complex.I • CFC.sqrt (1-B^2) := rfl
    change (1/4 : ℂ) • (1+1+(u : Mat d)+star (u : Mat d))=A
    rw [hstar,hu]
    dsimp [B]
    module

end
end E2.CompilerDomains
