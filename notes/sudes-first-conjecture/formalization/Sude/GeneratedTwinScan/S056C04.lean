import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117964845 117997613 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117964845 117997613).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117964845 117997613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117997613 118030381 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117997613 118030381).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117997613 118030381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118030381 118063149 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118030381 118063149).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118030381 118063149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118063149 118095917 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118063149 118095917).card = 152 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118063149 118095917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117964845 118030381).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 117964845 ≤ 117997613)
    (by decide : 117997613 ≤ 118030381) block0 block1

theorem join_0_1 : (twinPrimeSegment 118030381 118095917).card = 287 := by
  simpa using combineTwinPrimeSegments (by decide : 118030381 ≤ 118063149)
    (by decide : 118063149 ≤ 118095917) block2 block3

theorem join_1_0 : (twinPrimeSegment 117964845 118095917).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 117964845 ≤ 118030381)
    (by decide : 118030381 ≤ 118095917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117964845 118095917).card = 539 := join_1_0

end S056C04
end Sude.GeneratedTwinScan
