import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126877741 126910509 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126877741 126910509).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126877741 126910509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126910509 126943277 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126910509 126943277).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126910509 126943277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126943277 126976045 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126943277 126976045).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126943277 126976045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126976045 127008813 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126976045 127008813).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126976045 127008813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126877741 126943277).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 126877741 ≤ 126910509)
    (by decide : 126910509 ≤ 126943277) block0 block1

theorem join_0_1 : (twinPrimeSegment 126943277 127008813).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 126943277 ≤ 126976045)
    (by decide : 126976045 ≤ 127008813) block2 block3

theorem join_1_0 : (twinPrimeSegment 126877741 127008813).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 126877741 ≤ 126943277)
    (by decide : 126943277 ≤ 127008813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126877741 127008813).card = 502 := join_1_0

end S060C08
end Sude.GeneratedTwinScan
