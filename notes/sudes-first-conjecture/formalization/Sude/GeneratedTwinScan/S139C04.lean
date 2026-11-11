import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17089)) 292028461 292061229 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292028461 292061229).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17089 292028461 292061229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17090)) 292061229 292093997 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292061229 292093997).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17090 292061229 292093997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17091)) 292093997 292126765 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292093997 292126765).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17091 292093997 292126765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17092)) 292126765 292159533 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292126765 292159533).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17092 292126765 292159533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292028461 292093997).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 292028461 ≤ 292061229)
    (by decide : 292061229 ≤ 292093997) block0 block1

theorem join_0_1 : (twinPrimeSegment 292093997 292159533).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 292093997 ≤ 292126765)
    (by decide : 292126765 ≤ 292159533) block2 block3

theorem join_1_0 : (twinPrimeSegment 292028461 292159533).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 292028461 ≤ 292093997)
    (by decide : 292093997 ≤ 292159533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292028461 292159533).card = 489 := join_1_0

end S139C04
end Sude.GeneratedTwinScan
