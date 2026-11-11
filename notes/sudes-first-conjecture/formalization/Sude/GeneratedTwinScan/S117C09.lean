import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15702)) 246546477 246579245 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 246546477 246579245).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15702 246546477 246579245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15703)) 246579245 246612013 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 246579245 246612013).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15703 246579245 246612013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15704)) 246612013 246644781 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 246612013 246644781).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15704 246612013 246644781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15705)) 246644781 246677549 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 246644781 246677549).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15705 246644781 246677549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 246546477 246612013).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 246546477 ≤ 246579245)
    (by decide : 246579245 ≤ 246612013) block0 block1

theorem join_0_1 : (twinPrimeSegment 246612013 246677549).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 246612013 ≤ 246644781)
    (by decide : 246644781 ≤ 246677549) block2 block3

theorem join_1_0 : (twinPrimeSegment 246546477 246677549).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 246546477 ≤ 246612013)
    (by decide : 246612013 ≤ 246677549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 246546477 246677549).card = 461 := join_1_0

end S117C09
end Sude.GeneratedTwinScan
