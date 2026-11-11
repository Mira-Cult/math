import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102236205 102268973 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102236205 102268973).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102236205 102268973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102268973 102301741 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102268973 102301741).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102268973 102301741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102301741 102334509 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102301741 102334509).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102301741 102334509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102334509 102367277 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102334509 102367277).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102334509 102367277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102236205 102301741).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 102236205 ≤ 102268973)
    (by decide : 102268973 ≤ 102301741) block0 block1

theorem join_0_1 : (twinPrimeSegment 102301741 102367277).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 102301741 ≤ 102334509)
    (by decide : 102334509 ≤ 102367277) block2 block3

theorem join_1_0 : (twinPrimeSegment 102236205 102367277).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 102236205 ≤ 102301741)
    (by decide : 102301741 ≤ 102367277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102236205 102367277).card = 538 := join_1_0

end S048C12
end Sude.GeneratedTwinScan
