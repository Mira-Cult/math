import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78643245 78676013 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78643245 78676013).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78643245 78676013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78676013 78708781 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78676013 78708781).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78676013 78708781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78708781 78741549 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78708781 78741549).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78708781 78741549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78741549 78774317 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78741549 78774317).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78741549 78774317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78643245 78708781).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 78643245 ≤ 78676013)
    (by decide : 78676013 ≤ 78708781) block0 block1

theorem join_0_1 : (twinPrimeSegment 78708781 78774317).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 78708781 ≤ 78741549)
    (by decide : 78741549 ≤ 78774317) block2 block3

theorem join_1_0 : (twinPrimeSegment 78643245 78774317).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 78643245 ≤ 78708781)
    (by decide : 78708781 ≤ 78774317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78643245 78774317).card = 522 := join_1_0

end S037C08
end Sude.GeneratedTwinScan
