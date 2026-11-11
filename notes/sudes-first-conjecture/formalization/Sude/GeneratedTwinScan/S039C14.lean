import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83623981 83656749 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 83623981 83656749).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83623981 83656749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83656749 83689517 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83656749 83689517).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83656749 83689517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83689517 83722285 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83689517 83722285).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83689517 83722285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83722285 83755053 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83722285 83755053).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83722285 83755053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 83623981 83689517).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 83623981 ≤ 83656749)
    (by decide : 83656749 ≤ 83689517) block0 block1

theorem join_0_1 : (twinPrimeSegment 83689517 83755053).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 83689517 ≤ 83722285)
    (by decide : 83722285 ≤ 83755053) block2 block3

theorem join_1_0 : (twinPrimeSegment 83623981 83755053).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 83623981 ≤ 83689517)
    (by decide : 83689517 ≤ 83755053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 83623981 83755053).card = 542 := join_1_0

end S039C14
end Sude.GeneratedTwinScan
