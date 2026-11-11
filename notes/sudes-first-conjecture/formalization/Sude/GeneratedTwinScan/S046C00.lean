import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96469037 96501805 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96469037 96501805).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96469037 96501805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96501805 96534573 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96501805 96534573).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96501805 96534573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96534573 96567341 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96534573 96567341).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96534573 96567341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96567341 96600109 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96567341 96600109).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96567341 96600109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96469037 96534573).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 96501805)
    (by decide : 96501805 ≤ 96534573) block0 block1

theorem join_0_1 : (twinPrimeSegment 96534573 96600109).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 96534573 ≤ 96567341)
    (by decide : 96567341 ≤ 96600109) block2 block3

theorem join_1_0 : (twinPrimeSegment 96469037 96600109).card = 526 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 96534573)
    (by decide : 96534573 ≤ 96600109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96469037 96600109).card = 526 := join_1_0

end S046C00
end Sude.GeneratedTwinScan
