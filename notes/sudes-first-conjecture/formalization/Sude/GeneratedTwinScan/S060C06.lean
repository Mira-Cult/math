import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126615597 126648365 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126615597 126648365).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126615597 126648365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126648365 126681133 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126648365 126681133).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126648365 126681133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126681133 126713901 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126681133 126713901).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126681133 126713901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126713901 126746669 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126713901 126746669).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126713901 126746669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126615597 126681133).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 126615597 ≤ 126648365)
    (by decide : 126648365 ≤ 126681133) block0 block1

theorem join_0_1 : (twinPrimeSegment 126681133 126746669).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 126681133 ≤ 126713901)
    (by decide : 126713901 ≤ 126746669) block2 block3

theorem join_1_0 : (twinPrimeSegment 126615597 126746669).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 126615597 ≤ 126681133)
    (by decide : 126681133 ≤ 126746669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126615597 126746669).card = 520 := join_1_0

end S060C06
end Sude.GeneratedTwinScan
