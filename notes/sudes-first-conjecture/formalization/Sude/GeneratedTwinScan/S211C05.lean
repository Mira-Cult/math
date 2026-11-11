import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21052)) 443154477 443187245 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443154477 443187245).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21052 443154477 443187245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21052)) 443187245 443220013 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443187245 443220013).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21052 443187245 443220013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21053)) 443220013 443252781 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443220013 443252781).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21053 443220013 443252781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21054)) 443252781 443285549 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443252781 443285549).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21054 443252781 443285549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443154477 443220013).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 443154477 ≤ 443187245)
    (by decide : 443187245 ≤ 443220013) block0 block1

theorem join_0_1 : (twinPrimeSegment 443220013 443285549).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 443220013 ≤ 443252781)
    (by decide : 443252781 ≤ 443285549) block2 block3

theorem join_1_0 : (twinPrimeSegment 443154477 443285549).card = 403 := by
  simpa using combineTwinPrimeSegments (by decide : 443154477 ≤ 443220013)
    (by decide : 443220013 ≤ 443285549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443154477 443285549).card = 403 := join_1_0

end S211C05
end Sude.GeneratedTwinScan
