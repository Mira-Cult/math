import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58851373 58884141 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58851373 58884141).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58851373 58884141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58884141 58916909 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58884141 58916909).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58884141 58916909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58916909 58949677 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58916909 58949677).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58916909 58949677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58949677 58982445 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58949677 58982445).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58949677 58982445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 58851373 58916909).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 58851373 ≤ 58884141)
    (by decide : 58884141 ≤ 58916909) block0 block1

theorem join_0_1 : (twinPrimeSegment 58916909 58982445).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 58916909 ≤ 58949677)
    (by decide : 58949677 ≤ 58982445) block2 block3

theorem join_1_0 : (twinPrimeSegment 58851373 58982445).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 58851373 ≤ 58916909)
    (by decide : 58916909 ≤ 58982445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58851373 58982445).card = 550 := join_1_0

end S028C01
end Sude.GeneratedTwinScan
