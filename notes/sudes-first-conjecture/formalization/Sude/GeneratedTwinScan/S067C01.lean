import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140640301 140673069 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140640301 140673069).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140640301 140673069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140673069 140705837 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140673069 140705837).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140673069 140705837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140705837 140738605 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140705837 140738605).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140705837 140738605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140738605 140771373 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140738605 140771373).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140738605 140771373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140640301 140705837).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 140640301 ≤ 140673069)
    (by decide : 140673069 ≤ 140705837) block0 block1

theorem join_0_1 : (twinPrimeSegment 140705837 140771373).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 140705837 ≤ 140738605)
    (by decide : 140738605 ≤ 140771373) block2 block3

theorem join_1_0 : (twinPrimeSegment 140640301 140771373).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 140640301 ≤ 140705837)
    (by decide : 140705837 ≤ 140771373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140640301 140771373).card = 498 := join_1_0

end S067C01
end Sude.GeneratedTwinScan
