import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77070381 77103149 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77070381 77103149).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77070381 77103149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77103149 77135917 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77103149 77135917).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77103149 77135917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77135917 77168685 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77135917 77168685).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77135917 77168685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77168685 77201453 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77168685 77201453).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77168685 77201453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77070381 77135917).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 77070381 ≤ 77103149)
    (by decide : 77103149 ≤ 77135917) block0 block1

theorem join_0_1 : (twinPrimeSegment 77135917 77201453).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 77135917 ≤ 77168685)
    (by decide : 77168685 ≤ 77201453) block2 block3

theorem join_1_0 : (twinPrimeSegment 77070381 77201453).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 77070381 ≤ 77135917)
    (by decide : 77135917 ≤ 77201453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77070381 77201453).card = 529 := join_1_0

end S036C12
end Sude.GeneratedTwinScan
