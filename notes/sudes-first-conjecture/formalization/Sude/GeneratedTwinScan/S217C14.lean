import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21376)) 456917037 456949805 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456917037 456949805).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21376 456917037 456949805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21377)) 456949805 456982573 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456949805 456982573).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21377 456949805 456982573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21377)) 456982573 457015341 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456982573 457015341).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21377 456982573 457015341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21378)) 457015341 457048109 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457015341 457048109).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21378 457015341 457048109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456917037 456982573).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 456917037 ≤ 456949805)
    (by decide : 456949805 ≤ 456982573) block0 block1

theorem join_0_1 : (twinPrimeSegment 456982573 457048109).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 456982573 ≤ 457015341)
    (by decide : 457015341 ≤ 457048109) block2 block3

theorem join_1_0 : (twinPrimeSegment 456917037 457048109).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 456917037 ≤ 456982573)
    (by decide : 456982573 ≤ 457048109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456917037 457048109).card = 419 := join_1_0

end S217C14
end Sude.GeneratedTwinScan
