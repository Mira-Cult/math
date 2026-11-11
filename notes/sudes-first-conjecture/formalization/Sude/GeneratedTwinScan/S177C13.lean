import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19311)) 372899885 372932653 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372899885 372932653).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19311 372899885 372932653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19312)) 372932653 372965421 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372932653 372965421).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19312 372932653 372965421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19313)) 372965421 372998189 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372965421 372998189).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19313 372965421 372998189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19314)) 372998189 373030957 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372998189 373030957).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19314 372998189 373030957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372899885 372965421).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 372899885 ≤ 372932653)
    (by decide : 372932653 ≤ 372965421) block0 block1

theorem join_0_1 : (twinPrimeSegment 372965421 373030957).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 372965421 ≤ 372998189)
    (by decide : 372998189 ≤ 373030957) block2 block3

theorem join_1_0 : (twinPrimeSegment 372899885 373030957).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 372899885 ≤ 372965421)
    (by decide : 372965421 ≤ 373030957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372899885 373030957).card = 460 := join_1_0

end S177C13
end Sude.GeneratedTwinScan
