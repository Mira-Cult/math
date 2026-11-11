import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126746669 126779437 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126746669 126779437).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126746669 126779437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126779437 126812205 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126779437 126812205).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126779437 126812205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126812205 126844973 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126812205 126844973).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126812205 126844973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126844973 126877741 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126844973 126877741).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126844973 126877741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126746669 126812205).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 126746669 ≤ 126779437)
    (by decide : 126779437 ≤ 126812205) block0 block1

theorem join_0_1 : (twinPrimeSegment 126812205 126877741).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 126812205 ≤ 126844973)
    (by decide : 126844973 ≤ 126877741) block2 block3

theorem join_1_0 : (twinPrimeSegment 126746669 126877741).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 126746669 ≤ 126812205)
    (by decide : 126812205 ≤ 126877741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126746669 126877741).card = 474 := join_1_0

end S060C07
end Sude.GeneratedTwinScan
