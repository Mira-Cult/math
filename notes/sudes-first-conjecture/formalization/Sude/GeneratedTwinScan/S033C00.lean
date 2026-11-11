import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69206061 69238829 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69206061 69238829).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69206061 69238829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69238829 69271597 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69238829 69271597).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69238829 69271597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69271597 69304365 = 162 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69271597 69304365).card = 162 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69271597 69304365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69304365 69337133 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69304365 69337133).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69304365 69337133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69206061 69271597).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 69238829)
    (by decide : 69238829 ≤ 69271597) block0 block1

theorem join_0_1 : (twinPrimeSegment 69271597 69337133).card = 304 := by
  simpa using combineTwinPrimeSegments (by decide : 69271597 ≤ 69304365)
    (by decide : 69304365 ≤ 69337133) block2 block3

theorem join_1_0 : (twinPrimeSegment 69206061 69337133).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 69206061 ≤ 69271597)
    (by decide : 69271597 ≤ 69337133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69206061 69337133).card = 539 := join_1_0

end S033C00
end Sude.GeneratedTwinScan
