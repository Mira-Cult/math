import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147456045 147488813 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147456045 147488813).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147456045 147488813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147488813 147521581 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147488813 147521581).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147488813 147521581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147521581 147554349 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147521581 147554349).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147521581 147554349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147554349 147587117 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147554349 147587117).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147554349 147587117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147456045 147521581).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 147456045 ≤ 147488813)
    (by decide : 147488813 ≤ 147521581) block0 block1

theorem join_0_1 : (twinPrimeSegment 147521581 147587117).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 147521581 ≤ 147554349)
    (by decide : 147554349 ≤ 147587117) block2 block3

theorem join_1_0 : (twinPrimeSegment 147456045 147587117).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 147456045 ≤ 147521581)
    (by decide : 147521581 ≤ 147587117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147456045 147587117).card = 496 := join_1_0

end S070C05
end Sude.GeneratedTwinScan
