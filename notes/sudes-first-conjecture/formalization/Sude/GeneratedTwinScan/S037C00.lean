import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77594669 77627437 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77594669 77627437).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77594669 77627437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77627437 77660205 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77627437 77660205).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77627437 77660205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77660205 77692973 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77660205 77692973).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77660205 77692973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77692973 77725741 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77692973 77725741).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77692973 77725741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77594669 77660205).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 77627437)
    (by decide : 77627437 ≤ 77660205) block0 block1

theorem join_0_1 : (twinPrimeSegment 77660205 77725741).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 77660205 ≤ 77692973)
    (by decide : 77692973 ≤ 77725741) block2 block3

theorem join_1_0 : (twinPrimeSegment 77594669 77725741).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 77594669 ≤ 77660205)
    (by decide : 77660205 ≤ 77725741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77594669 77725741).card = 515 := join_1_0

end S037C00
end Sude.GeneratedTwinScan
