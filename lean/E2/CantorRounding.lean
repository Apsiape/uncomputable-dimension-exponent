import E2.CarryTools
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace E2
noncomputable section
open scoped ComplexOrder Matrix.Norms.L2Operator
open Companion.Analytic

theorem cantorCoordinate_continuous : Continuous cantorCoordinate := by
  have he : cantorCoordinate=(fun b => ∑' j,cantorTerm b j) := funext cantorCoordinate_eq_tsum
  rw [he]
  apply continuous_tsum
  · intro j
    exact (continuous_of_discreteTopology (f:=fun z : Bool => if z then (3/4:ℝ)*cantorWeight j else 0)).comp (continuous_apply j)
  · exact (summable_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)).mul_left (3/4)
  · intro j b
    rw [Real.norm_eq_abs,abs_of_nonneg (cantorTerm_bounds b j).1]
    exact (cantorTerm_bounds b j).2

theorem cantorSet_compact : IsCompact cantorSet := isCompact_range cantorCoordinate_continuous

theorem cantorSet_nonempty : cantorSet.Nonempty := ⟨0,⟨fun _ => false,cantorCoordinate_zero⟩⟩

theorem cantor_nearest_exists (x : ℝ) : ∃ y∈cantorSet,Metric.infDist x cantorSet=dist x y :=
  cantorSet_compact.exists_infDist_eq_dist cantorSet_nonempty x

def cantorRound (x : ℝ) : ℝ := (cantor_nearest_exists x).choose

theorem cantorRound_mem (x : ℝ) : cantorRound x∈cantorSet := (cantor_nearest_exists x).choose_spec.1

theorem cantorRound_error (x : ℝ) : |cantorRound x-x|=Metric.infDist x cantorSet := by
  calc
    _ = dist x (cantorRound x) := by rw [Real.dist_eq,abs_sub_comm]
    _ = _ := (cantor_nearest_exists x).choose_spec.2.symm

theorem cantor_distance_lipschitz : LipschitzWith 1 (fun x => Metric.infDist x cantorSet) :=
  Metric.lipschitz_infDist_pt cantorSet

theorem selfadjoint_state_commutator {d : ℕ} (s : State d) (E : Mat d) (hE : E.IsHermitian) :
    hs (comm E s.xi)≤2*weighted s E := by
  have he : hs (s.xi*E)=hs (E*s.xi) := by
    change hsNorm (s.xi*E)=hsNorm (E*s.xi)
    rw [← hsNorm_conjTranspose (s.xi*E),Matrix.conjTranspose_mul,hE.eq,s.xi_positive.isHermitian.eq]
  exact (hs_sub_le (E*s.xi) (s.xi*E)).trans (by rw [he]; change _≤2*hs (E*s.xi); linarith)

theorem cantor_spectral_rounding {d : ℕ} (s : State d) (A : Mat d) (hA : A.IsHermitian) :
    HasCantorSpectrum (matrixFunction cantorRound A) ∧
    weighted s (matrixFunction cantorRound A-A)=weighted s (matrixFunction (fun x => Metric.infDist x cantorSet) A) ∧
    hs (comm (matrixFunction cantorRound A) s.xi)≤
      hs (comm A s.xi)+2*weighted s (matrixFunction cantorRound A-A) := by
  have hR := matrix_function_hermitian hA cantorRound
  have hD := matrix_function_hermitian hA (fun x => Metric.infDist x cantorSet)
  have hE : (matrixFunction cantorRound A-A).IsHermitian := hR.sub hA
  have he : matrixFunction cantorRound A-A=matrixFunction (fun x => cantorRound x-x) A := by
    conv_lhs => rhs; rw [← matrix_function_id hA]
    exact matrix_function_sub _ _ _
  have hgram : (matrixFunction cantorRound A-A).conjTranspose*(matrixFunction cantorRound A-A)=
      (matrixFunction (fun x => Metric.infDist x cantorSet) A).conjTranspose*
        matrixFunction (fun x => Metric.infDist x cantorSet) A := by
    rw [hE.eq,hD.eq,he,matrix_function_mul,matrix_function_mul]
    apply matrix_function_congr hA
    intro x hx
    have hh := congrArg (fun z : ℝ => z^2) (cantorRound_error x)
    rw [sq_abs] at hh
    simpa only [pow_two] using hh
  refine ⟨⟨hR,?_⟩,?_,?_⟩
  · rw [matrix_function_spectrum hA]
    rintro _ ⟨x,hx,rfl⟩
    exact cantorRound_mem x
  · apply (sq_eq_sq₀ (weighted_nonneg s _) (weighted_nonneg s _)).mp
    unfold weighted
    rw [hs_square_gram,hs_square_gram,hgram]
  · have heq : matrixFunction cantorRound A=A+(matrixFunction cantorRound A-A) := by abel
    have hc : comm (matrixFunction cantorRound A) s.xi=comm A s.xi+comm (matrixFunction cantorRound A-A) s.xi := by
      conv_lhs => rw [heq]
      simp only [comm,Companion.Analytic.comm,Matrix.add_mul,Matrix.mul_add]
      abel
    rw [hc]
    exact (hsNorm_add_le _ _).trans (add_le_add le_rfl (selfadjoint_state_commutator s _ hE))

end
end E2
