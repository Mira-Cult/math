import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13273)) 176160813 176193581 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176160813 176193581).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13273 176160813 176193581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13275)) 176193581 176226349 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176193581 176226349).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13275 176193581 176226349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13276)) 176226349 176259117 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176226349 176259117).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13276 176226349 176259117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13277)) 176259117 176291885 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176259117 176291885).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13277 176259117 176291885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176160813 176226349).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 176193581)
    (by decide : 176193581 ≤ 176226349) block0 block1

theorem join_0_1 : (twinPrimeSegment 176226349 176291885).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 176226349 ≤ 176259117)
    (by decide : 176259117 ≤ 176291885) block2 block3

theorem join_1_0 : (twinPrimeSegment 176160813 176291885).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 176226349)
    (by decide : 176226349 ≤ 176291885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176160813 176291885).card = 459 := join_1_0

end S084C00
end Sude.GeneratedTwinScan
