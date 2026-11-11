import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148504621 148537389 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148504621 148537389).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148504621 148537389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148537389 148570157 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148537389 148570157).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148537389 148570157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148570157 148602925 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148570157 148602925).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148570157 148602925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148602925 148635693 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148602925 148635693).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148602925 148635693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148504621 148570157).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 148504621 ≤ 148537389)
    (by decide : 148537389 ≤ 148570157) block0 block1

theorem join_0_1 : (twinPrimeSegment 148570157 148635693).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 148570157 ≤ 148602925)
    (by decide : 148602925 ≤ 148635693) block2 block3

theorem join_1_0 : (twinPrimeSegment 148504621 148635693).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 148504621 ≤ 148570157)
    (by decide : 148570157 ≤ 148635693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148504621 148635693).card = 499 := join_1_0

end S070C13
end Sude.GeneratedTwinScan
