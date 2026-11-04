import E2.CompilerAnd
import E2.MatrixFunctions

namespace E2.CompilerDomains
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

def decodeProjection {d : ℕ} (R : Mat d) : Mat d := (1/2 : ℂ) • (1+R)
def encodeProjection {d : ℕ} (P : Mat d) : Mat d := (2 : ℂ) • P-1

theorem decode_projection {d : ℕ} (R : Mat d) (hR : Domain.reflection.Holds R) :
    Domain.projection.Holds (decodeProjection R) := by
  constructor
  · simp [decodeProjection,Matrix.conjTranspose_smul,hR.1]
  · simp only [decodeProjection,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    have h : (1+R)*(1+R) = (2:ℂ) • (1+R) := by
      simp only [Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,hR.2]
      module
    rw [h,smul_smul]
    norm_num

theorem encode_projection {d : ℕ} (P : Mat d) (hP : Domain.projection.Holds P) :
    Domain.reflection.Holds (encodeProjection P) := by
  constructor
  · simp [encodeProjection,Matrix.conjTranspose_smul,hP.1]
  · simp only [encodeProjection,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,
      Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,smul_smul,hP.2]
    module

@[simp] theorem decode_encode_projection {d : ℕ} (P : Mat d) :
    decodeProjection (encodeProjection P)=P := by
  simp only [decodeProjection,encodeProjection]
  module

def decodePositive {d : ℕ} (U : Mat d) : Mat d :=
  (1/4 : ℂ) • (1+1+U+U.conjTranspose)

/-- Exact positive-contraction domain, with no approximation or state change. -/
theorem decode_positive {d : ℕ} (U : Mat d) (hU : Domain.unitary.Holds U) :
    Domain.positiveContraction.Holds (decodePositive U) := by
  have hplus : decodePositive U = (1/4 : ℂ) • ((1+U).conjTranspose*(1+U)) := by
    simp only [decodePositive,Matrix.conjTranspose_add,Matrix.conjTranspose_one,
      Matrix.add_mul,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,hU.1]
    module
  have hminus : 1-decodePositive U = (1/4 : ℂ) • ((1-U).conjTranspose*(1-U)) := by
    simp only [decodePositive,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,
      Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,hU.1]
    module
  constructor
  · rw [hplus]
    exact (Matrix.posSemidef_conjTranspose_mul_self (1+U)).smul (by exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)
  · rw [hminus]
    exact (Matrix.posSemidef_conjTranspose_mul_self (1-U)).smul (by exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩)

theorem reflection_product_unitary {d : ℕ} (A B : Mat d)
    (hA : Domain.reflection.Holds A) (hB : Domain.reflection.Holds B) :
    Domain.unitary.Holds (A*B) := by
  constructor
  · simp only [Matrix.conjTranspose_mul,hA.1,hB.1]
    calc
      _ = B*(A*A)*B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA.2,Matrix.mul_one,hB.2]
  · simp only [Matrix.conjTranspose_mul,hA.1,hB.1]
    calc
      _ = A*(B*B)*A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB.2,Matrix.mul_one,hA.2]

def controlled {d : ℕ} (E S : Mat d) : Mat d := 1-E+E*S

/-- The controlled Boolean reflection has its exact declared domain whenever
the control projection commutes with the source reflection. -/
theorem controlled_reflection {d : ℕ} (E S : Mat d)
    (hE : Domain.projection.Holds E) (hS : Domain.reflection.Holds S)
    (hES : E*S=S*E) : Domain.reflection.Holds (controlled E S) := by
  constructor
  · simp only [controlled,Matrix.conjTranspose_add,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one,Matrix.conjTranspose_mul,hE.1,hS.1]
    rw [hES]
  · have h1 : E*S*E=E*S := by
      calc
        _ = E*(S*E) := by rw [Matrix.mul_assoc]
        _ = E*(E*S) := by rw [hES]
        _ = E*S := by rw [← Matrix.mul_assoc,hE.2]
    have h2 : E*S*E*S=E := by
      rw [h1,Matrix.mul_assoc,hS.2,Matrix.mul_one]
    have h3 : S*E=E*S := hES.symm
    calc
      _ = 1-E-E+E*S+E*E-E*E*S+E*S-E*S*E+E*S*E*S := by
        unfold controlled
        noncomm_ring
      _ = 1 := by rw [h2,hE.2,h1]; abel

end
end E2.CompilerDomains
