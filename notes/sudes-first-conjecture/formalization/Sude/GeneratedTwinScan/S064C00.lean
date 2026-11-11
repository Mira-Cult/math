import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134217773 134250541 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134217773 134250541).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134217773 134250541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134250541 134283309 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134250541 134283309).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134250541 134283309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134283309 134316077 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134283309 134316077).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134283309 134316077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134316077 134348845 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134316077 134348845).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134316077 134348845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134217773 134283309).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 134250541)
    (by decide : 134250541 ≤ 134283309) block0 block1

theorem join_0_1 : (twinPrimeSegment 134283309 134348845).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 134283309 ≤ 134316077)
    (by decide : 134316077 ≤ 134348845) block2 block3

theorem join_1_0 : (twinPrimeSegment 134217773 134348845).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 134283309)
    (by decide : 134283309 ≤ 134348845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134217773 134348845).card = 488 := join_1_0

end S064C00
end Sude.GeneratedTwinScan
