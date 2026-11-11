import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14460)) 209059885 209092653 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209059885 209092653).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14460 209059885 209092653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14461)) 209092653 209125421 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209092653 209125421).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14461 209092653 209125421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14462)) 209125421 209158189 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209125421 209158189).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14462 209125421 209158189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14463)) 209158189 209190957 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209158189 209190957).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14463 209158189 209190957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209059885 209125421).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 209059885 ≤ 209092653)
    (by decide : 209092653 ≤ 209125421) block0 block1

theorem join_0_1 : (twinPrimeSegment 209125421 209190957).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 209125421 ≤ 209158189)
    (by decide : 209158189 ≤ 209190957) block2 block3

theorem join_1_0 : (twinPrimeSegment 209059885 209190957).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 209059885 ≤ 209125421)
    (by decide : 209125421 ≤ 209190957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209059885 209190957).card = 481 := join_1_0

end S099C11
end Sude.GeneratedTwinScan
