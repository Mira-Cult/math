import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16029)) 256901165 256933933 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256901165 256933933).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16029 256901165 256933933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16030)) 256933933 256966701 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256933933 256966701).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16030 256933933 256966701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16031)) 256966701 256999469 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256966701 256999469).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16031 256966701 256999469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16032)) 256999469 257032237 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256999469 257032237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16032 256999469 257032237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256901165 256966701).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 256901165 ≤ 256933933)
    (by decide : 256933933 ≤ 256966701) block0 block1

theorem join_0_1 : (twinPrimeSegment 256966701 257032237).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 256966701 ≤ 256999469)
    (by decide : 256999469 ≤ 257032237) block2 block3

theorem join_1_0 : (twinPrimeSegment 256901165 257032237).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 256901165 ≤ 256966701)
    (by decide : 256966701 ≤ 257032237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256901165 257032237).card = 467 := join_1_0

end S122C08
end Sude.GeneratedTwinScan
