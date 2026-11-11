import Sude.PrefixLStage0Values
import Sude.PrefixStageSeparation
import Sude.GeneratedPrefix.LStage1.All

/-! Actual separation of the first L stage from the complete checked second stage. -/
namespace Sude.GeneratedPrefix
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[irreducible] def LStage1.checkedLows : List ℕ := LStage1.lows

theorem LStage1.checkedLows_valid :
    PrefixStageBlock 4 55000000 16178779 19235257 LStage1.checkedLows := by
  rw [LStage1.checkedLows]
  exact LStage1.valid

theorem LStage0.checkedLows_valid :
    PrefixStageBlock 2 55000000 13005401 15965249 LStage0.checkedLows := by
  rw [LStage0.checkedLows]
  exact LStage0.valid

theorem LStage1.checkedLows_length : LStage1.checkedLows.length = 14448 := by
  rw [LStage1.checkedLows]
  exact LStage1.length

/-- This separates all 14,448 certified stage-zero pairs from all 14,448
certified stage-one pairs, including both endpoints of every pair. -/
theorem firstStage_disjoint_secondStageCheckpoint :
    Disjoint (pairFootprint LStage0.checkedLows.toFinset 2)
      (pairFootprint LStage1.checkedLows.toFinset 4) :=
  PrefixStageBlock.footprints_disjoint LStage0.checkedLows_valid LStage1.checkedLows_valid (by decide)

end
end Sude.GeneratedPrefix
