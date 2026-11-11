import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22470)) 504889389 504922157 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504889389 504922157).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22470 504889389 504922157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22471)) 504922157 504954925 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504922157 504954925).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22471 504922157 504954925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22471)) 504954925 504987693 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504954925 504987693).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22471 504954925 504987693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22472)) 504987693 505020461 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504987693 505020461).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22472 504987693 505020461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504889389 504954925).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 504889389 ≤ 504922157)
    (by decide : 504922157 ≤ 504954925) block0 block1

theorem join_0_1 : (twinPrimeSegment 504954925 505020461).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 504954925 ≤ 504987693)
    (by decide : 504987693 ≤ 505020461) block2 block3

theorem join_1_0 : (twinPrimeSegment 504889389 505020461).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 504889389 ≤ 504954925)
    (by decide : 504954925 ≤ 505020461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504889389 505020461).card = 423 := join_1_0

end S240C12
end Sude.GeneratedTwinScan
