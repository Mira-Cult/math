import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21816)) 475922477 475955245 = 87 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475922477 475955245).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21816 475922477 475955245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21817)) 475955245 475988013 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475955245 475988013).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21817 475955245 475988013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21817)) 475988013 476020781 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475988013 476020781).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21817 475988013 476020781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21818)) 476020781 476053549 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476020781 476053549).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21818 476020781 476053549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475922477 475988013).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 475922477 ≤ 475955245)
    (by decide : 475955245 ≤ 475988013) block0 block1

theorem join_0_1 : (twinPrimeSegment 475988013 476053549).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 475988013 ≤ 476020781)
    (by decide : 476020781 ≤ 476053549) block2 block3

theorem join_1_0 : (twinPrimeSegment 475922477 476053549).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 475922477 ≤ 475988013)
    (by decide : 475988013 ≤ 476053549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475922477 476053549).card = 398 := join_1_0

end S226C15
end Sude.GeneratedTwinScan
