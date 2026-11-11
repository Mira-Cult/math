import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61472813 61505581 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61472813 61505581).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61472813 61505581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61505581 61538349 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61505581 61538349).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61505581 61538349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61538349 61571117 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61538349 61571117).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61538349 61571117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61571117 61603885 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61571117 61603885).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61571117 61603885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61472813 61538349).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 61472813 ≤ 61505581)
    (by decide : 61505581 ≤ 61538349) block0 block1

theorem join_0_1 : (twinPrimeSegment 61538349 61603885).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 61538349 ≤ 61571117)
    (by decide : 61571117 ≤ 61603885) block2 block3

theorem join_1_0 : (twinPrimeSegment 61472813 61603885).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 61472813 ≤ 61538349)
    (by decide : 61538349 ≤ 61603885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61472813 61603885).card = 553 := join_1_0

end S029C05
end Sude.GeneratedTwinScan
