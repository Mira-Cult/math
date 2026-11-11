import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22406)) 502005805 502038573 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502005805 502038573).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22406 502005805 502038573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22406)) 502038573 502071341 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502038573 502071341).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22406 502038573 502071341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22407)) 502071341 502104109 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502071341 502104109).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22407 502071341 502104109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22408)) 502104109 502136877 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502104109 502136877).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22408 502104109 502136877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502005805 502071341).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 502005805 ≤ 502038573)
    (by decide : 502038573 ≤ 502071341) block0 block1

theorem join_0_1 : (twinPrimeSegment 502071341 502136877).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 502071341 ≤ 502104109)
    (by decide : 502104109 ≤ 502136877) block2 block3

theorem join_1_0 : (twinPrimeSegment 502005805 502136877).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 502005805 ≤ 502071341)
    (by decide : 502071341 ≤ 502136877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502005805 502136877).card = 419 := join_1_0

end S239C06
end Sude.GeneratedTwinScan
