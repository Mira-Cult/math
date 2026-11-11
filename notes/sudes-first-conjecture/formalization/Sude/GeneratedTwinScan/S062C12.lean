import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131596333 131629101 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131596333 131629101).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131596333 131629101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131629101 131661869 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131629101 131661869).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131629101 131661869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131661869 131694637 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131661869 131694637).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131661869 131694637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131694637 131727405 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131694637 131727405).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131694637 131727405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131596333 131661869).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 131596333 ≤ 131629101)
    (by decide : 131629101 ≤ 131661869) block0 block1

theorem join_0_1 : (twinPrimeSegment 131661869 131727405).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 131661869 ≤ 131694637)
    (by decide : 131694637 ≤ 131727405) block2 block3

theorem join_1_0 : (twinPrimeSegment 131596333 131727405).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 131596333 ≤ 131661869)
    (by decide : 131661869 ≤ 131727405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131596333 131727405).card = 492 := join_1_0

end S062C12
end Sude.GeneratedTwinScan
