import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118620205 118652973 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118620205 118652973).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118620205 118652973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118652973 118685741 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118652973 118685741).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118652973 118685741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118685741 118718509 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118685741 118718509).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118685741 118718509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118718509 118751277 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118718509 118751277).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118718509 118751277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118620205 118685741).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 118620205 ≤ 118652973)
    (by decide : 118652973 ≤ 118685741) block0 block1

theorem join_0_1 : (twinPrimeSegment 118685741 118751277).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 118685741 ≤ 118718509)
    (by decide : 118718509 ≤ 118751277) block2 block3

theorem join_1_0 : (twinPrimeSegment 118620205 118751277).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 118620205 ≤ 118685741)
    (by decide : 118685741 ≤ 118751277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118620205 118751277).card = 485 := join_1_0

end S056C09
end Sude.GeneratedTwinScan
