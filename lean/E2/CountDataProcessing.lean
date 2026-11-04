import E2.CountCQ
import QIT.Information.CQChannel
import QIT.Information.Entropy.StrongSubadditivity

namespace E2.CountCQ.Family
noncomputable section
open scoped BigOperators ComplexOrder NNReal
variable {ι b c : Type*} [Fintype ι] [DecidableEq ι] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c]

def map (F : Family ι b) (T : QIT.Channel b c) : Family ι c where
  mass := F.mass
  matrix x := T.map (F.matrix x)
  nonneg := F.nonneg
  positive x := T.mapsPositive _ (F.positive x)
  trace x := (T.tracePreserving _).trans (F.trace x)
  total := F.total

theorem map_normalized (F : Family ι b) (T : QIT.Channel b c) (fallback : QIT.State b) (x : ι) :
    (F.map T).normalized (T.applyState fallback) x = T.applyState (F.normalized fallback x) := by
  apply QIT.State.ext
  change (if F.mass x=0 then T.map fallback.matrix else (((F.mass x)⁻¹:ℝ):ℂ) • T.map (F.matrix x)) =
    T.map (if F.mass x=0 then fallback.matrix else (((F.mass x)⁻¹:ℝ):ℂ) • F.matrix x)
  split_ifs <;> simp only [map_smul]

theorem map_cq (F : Family ι b) (T : QIT.Channel b c) (fallback : QIT.State b) :
    ((F.map T).ensemble (T.applyState fallback)).cqState =
      ((QIT.Channel.idChannel ι).prod T).applyState (F.ensemble fallback).cqState := by
  apply QIT.State.ext
  rw [QIT.applyState_id_prod_cqState_matrix, QIT.Ensemble.cqState_matrix]
  apply Finset.sum_congr rfl
  intro x _
  rw [show ((F.map T).ensemble (T.applyState fallback)).states x = T.applyState ((F.ensemble fallback).states x) from F.map_normalized T fallback x]
  rfl

theorem cq_conditional (F : Family ι b) (fallback : QIT.State b) :
    (F.ensemble fallback).cqState.conditionalEntropy = F.conditional fallback := by
  rw [QIT.State.conditionalEntropy_eq, QIT.Ensemble.cqState_marginalB_eq_averageState, ensemble_average, cq_entropy]
  rfl

theorem conditional_dataProcessing (F : Family ι b) (T : QIT.Channel b c) (fallback : QIT.State b) :
    F.conditional fallback ≤ (F.map T).conditional (T.applyState fallback) := by
  let rho := (F.ensemble fallback).cqState
  have hd := QIT.mutualInformation_dataProcessing_local_channels_ge rho (QIT.Channel.idChannel ι) T
  have hm : (((QIT.Channel.idChannel ι).prod T).applyState rho).marginalA = rho.marginalA := by
    rw [QIT.State.marginalA_applyState_prod, QIT.State.applyState_idChannel]
  have hmap : ((QIT.Channel.idChannel ι).prod T).applyState rho = ((F.map T).ensemble (T.applyState fallback)).cqState := (F.map_cq T fallback).symm
  rw [QIT.mutualInformation, QIT.mutualInformation, hm] at hd
  have h1 := F.cq_conditional fallback
  have h2 := (F.map T).cq_conditional (T.applyState fallback)
  rw [QIT.State.conditionalEntropy_eq] at h1 h2
  rw [←hmap] at h2
  dsimp [rho] at hd
  linarith

end
end E2.CountCQ.Family
