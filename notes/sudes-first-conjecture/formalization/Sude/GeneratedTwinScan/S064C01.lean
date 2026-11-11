import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134348845 134381613 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134348845 134381613).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134348845 134381613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134381613 134414381 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134381613 134414381).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134381613 134414381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134414381 134447149 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134414381 134447149).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134414381 134447149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134447149 134479917 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134447149 134479917).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134447149 134479917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134348845 134414381).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 134348845 ≤ 134381613)
    (by decide : 134381613 ≤ 134414381) block0 block1

theorem join_0_1 : (twinPrimeSegment 134414381 134479917).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 134414381 ≤ 134447149)
    (by decide : 134447149 ≤ 134479917) block2 block3

theorem join_1_0 : (twinPrimeSegment 134348845 134479917).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 134348845 ≤ 134414381)
    (by decide : 134414381 ≤ 134479917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134348845 134479917).card = 513 := join_1_0

end S064C01
end Sude.GeneratedTwinScan
