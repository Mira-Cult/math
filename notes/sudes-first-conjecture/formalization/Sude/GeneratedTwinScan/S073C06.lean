import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12406)) 153878573 153911341 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153878573 153911341).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12406 153878573 153911341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12407)) 153911341 153944109 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153911341 153944109).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12407 153911341 153944109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12408)) 153944109 153976877 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153944109 153976877).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12408 153944109 153976877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12410)) 153976877 154009645 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153976877 154009645).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12410 153976877 154009645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153878573 153944109).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 153878573 ≤ 153911341)
    (by decide : 153911341 ≤ 153944109) block0 block1

theorem join_0_1 : (twinPrimeSegment 153944109 154009645).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 153944109 ≤ 153976877)
    (by decide : 153976877 ≤ 154009645) block2 block3

theorem join_1_0 : (twinPrimeSegment 153878573 154009645).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 153878573 ≤ 153944109)
    (by decide : 153944109 ≤ 154009645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153878573 154009645).card = 498 := join_1_0

end S073C06
end Sude.GeneratedTwinScan
