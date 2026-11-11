import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111935533 111968301 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111935533 111968301).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111935533 111968301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111968301 112001069 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111968301 112001069).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111968301 112001069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112001069 112033837 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112001069 112033837).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112001069 112033837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112033837 112066605 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112033837 112066605).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112033837 112066605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111935533 112001069).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 111935533 ≤ 111968301)
    (by decide : 111968301 ≤ 112001069) block0 block1

theorem join_0_1 : (twinPrimeSegment 112001069 112066605).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 112001069 ≤ 112033837)
    (by decide : 112033837 ≤ 112066605) block2 block3

theorem join_1_0 : (twinPrimeSegment 111935533 112066605).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 111935533 ≤ 112001069)
    (by decide : 112001069 ≤ 112066605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111935533 112066605).card = 502 := join_1_0

end S053C06
end Sude.GeneratedTwinScan
