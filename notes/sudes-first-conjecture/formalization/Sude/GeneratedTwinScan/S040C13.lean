import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85590061 85622829 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85590061 85622829).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85590061 85622829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85622829 85655597 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85622829 85655597).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85622829 85655597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85655597 85688365 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85655597 85688365).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85655597 85688365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85688365 85721133 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85688365 85721133).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85688365 85721133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85590061 85655597).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 85590061 ≤ 85622829)
    (by decide : 85622829 ≤ 85655597) block0 block1

theorem join_0_1 : (twinPrimeSegment 85655597 85721133).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 85655597 ≤ 85688365)
    (by decide : 85688365 ≤ 85721133) block2 block3

theorem join_1_0 : (twinPrimeSegment 85590061 85721133).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 85590061 ≤ 85655597)
    (by decide : 85655597 ≤ 85721133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85590061 85721133).card = 496 := join_1_0

end S040C13
end Sude.GeneratedTwinScan
