import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116129837 116162605 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116129837 116162605).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116129837 116162605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116162605 116195373 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116162605 116195373).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116162605 116195373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116195373 116228141 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116195373 116228141).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116195373 116228141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116228141 116260909 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 116228141 116260909).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116228141 116260909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116129837 116195373).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 116129837 ≤ 116162605)
    (by decide : 116162605 ≤ 116195373) block0 block1

theorem join_0_1 : (twinPrimeSegment 116195373 116260909).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 116195373 ≤ 116228141)
    (by decide : 116228141 ≤ 116260909) block2 block3

theorem join_1_0 : (twinPrimeSegment 116129837 116260909).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 116129837 ≤ 116195373)
    (by decide : 116195373 ≤ 116260909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116129837 116260909).card = 499 := join_1_0

end S055C06
end Sude.GeneratedTwinScan
