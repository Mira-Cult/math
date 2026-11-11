import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22554)) 508690477 508723245 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508690477 508723245).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22554 508690477 508723245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22555)) 508723245 508756013 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508723245 508756013).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22555 508723245 508756013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22556)) 508756013 508788781 = 88 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508756013 508788781).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22556 508756013 508788781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22557)) 508788781 508821549 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508788781 508821549).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22557 508788781 508821549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508690477 508756013).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 508690477 ≤ 508723245)
    (by decide : 508723245 ≤ 508756013) block0 block1

theorem join_0_1 : (twinPrimeSegment 508756013 508821549).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 508756013 ≤ 508788781)
    (by decide : 508788781 ≤ 508821549) block2 block3

theorem join_1_0 : (twinPrimeSegment 508690477 508821549).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 508690477 ≤ 508756013)
    (by decide : 508756013 ≤ 508821549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508690477 508821549).card = 425 := join_1_0

end S242C09
end Sude.GeneratedTwinScan
