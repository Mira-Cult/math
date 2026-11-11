import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114688045 114720813 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114688045 114720813).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114688045 114720813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114720813 114753581 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114720813 114753581).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114720813 114753581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114753581 114786349 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114753581 114786349).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114753581 114786349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114786349 114819117 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114786349 114819117).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114786349 114819117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114688045 114753581).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 114688045 ≤ 114720813)
    (by decide : 114720813 ≤ 114753581) block0 block1

theorem join_0_1 : (twinPrimeSegment 114753581 114819117).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 114753581 ≤ 114786349)
    (by decide : 114786349 ≤ 114819117) block2 block3

theorem join_1_0 : (twinPrimeSegment 114688045 114819117).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 114688045 ≤ 114753581)
    (by decide : 114753581 ≤ 114819117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114688045 114819117).card = 493 := join_1_0

end S054C11
end Sude.GeneratedTwinScan
