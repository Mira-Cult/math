import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90308653 90341421 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90308653 90341421).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90308653 90341421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90341421 90374189 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90341421 90374189).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90341421 90374189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90374189 90406957 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90374189 90406957).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90374189 90406957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90406957 90439725 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90406957 90439725).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90406957 90439725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90308653 90374189).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 90308653 ≤ 90341421)
    (by decide : 90341421 ≤ 90374189) block0 block1

theorem join_0_1 : (twinPrimeSegment 90374189 90439725).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 90374189 ≤ 90406957)
    (by decide : 90406957 ≤ 90439725) block2 block3

theorem join_1_0 : (twinPrimeSegment 90308653 90439725).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 90308653 ≤ 90374189)
    (by decide : 90374189 ≤ 90439725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90308653 90439725).card = 534 := join_1_0

end S043C01
end Sude.GeneratedTwinScan
