import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113377325 113410093 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113377325 113410093).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113377325 113410093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113410093 113442861 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113410093 113442861).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113410093 113442861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113442861 113475629 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113442861 113475629).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113442861 113475629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113475629 113508397 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113475629 113508397).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113475629 113508397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113377325 113442861).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 113377325 ≤ 113410093)
    (by decide : 113410093 ≤ 113442861) block0 block1

theorem join_0_1 : (twinPrimeSegment 113442861 113508397).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 113442861 ≤ 113475629)
    (by decide : 113475629 ≤ 113508397) block2 block3

theorem join_1_0 : (twinPrimeSegment 113377325 113508397).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 113377325 ≤ 113442861)
    (by decide : 113442861 ≤ 113508397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113377325 113508397).card = 497 := join_1_0

end S054C01
end Sude.GeneratedTwinScan
