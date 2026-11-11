import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65273901 65306669 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65273901 65306669).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65273901 65306669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65306669 65339437 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65306669 65339437).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65306669 65339437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65339437 65372205 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65339437 65372205).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65339437 65372205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65372205 65404973 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65372205 65404973).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65372205 65404973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65273901 65339437).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 65273901 ≤ 65306669)
    (by decide : 65306669 ≤ 65339437) block0 block1

theorem join_0_1 : (twinPrimeSegment 65339437 65404973).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 65339437 ≤ 65372205)
    (by decide : 65372205 ≤ 65404973) block2 block3

theorem join_1_0 : (twinPrimeSegment 65273901 65404973).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 65273901 ≤ 65339437)
    (by decide : 65339437 ≤ 65404973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65273901 65404973).card = 505 := join_1_0

end S031C02
end Sude.GeneratedTwinScan
