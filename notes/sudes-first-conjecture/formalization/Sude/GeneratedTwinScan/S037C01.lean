import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77725741 77758509 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77725741 77758509).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77725741 77758509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77758509 77791277 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77758509 77791277).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77758509 77791277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77791277 77824045 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77791277 77824045).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77791277 77824045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77824045 77856813 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77824045 77856813).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77824045 77856813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77725741 77791277).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 77725741 ≤ 77758509)
    (by decide : 77758509 ≤ 77791277) block0 block1

theorem join_0_1 : (twinPrimeSegment 77791277 77856813).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 77791277 ≤ 77824045)
    (by decide : 77824045 ≤ 77856813) block2 block3

theorem join_1_0 : (twinPrimeSegment 77725741 77856813).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 77725741 ≤ 77791277)
    (by decide : 77791277 ≤ 77856813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77725741 77856813).card = 538 := join_1_0

end S037C01
end Sude.GeneratedTwinScan
