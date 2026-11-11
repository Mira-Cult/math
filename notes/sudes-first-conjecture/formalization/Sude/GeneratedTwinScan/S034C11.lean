import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72745005 72777773 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72745005 72777773).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72745005 72777773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72777773 72810541 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72777773 72810541).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72777773 72810541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72810541 72843309 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72810541 72843309).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72810541 72843309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72843309 72876077 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72843309 72876077).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72843309 72876077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72745005 72810541).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 72745005 ≤ 72777773)
    (by decide : 72777773 ≤ 72810541) block0 block1

theorem join_0_1 : (twinPrimeSegment 72810541 72876077).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 72810541 ≤ 72843309)
    (by decide : 72843309 ≤ 72876077) block2 block3

theorem join_1_0 : (twinPrimeSegment 72745005 72876077).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 72745005 ≤ 72810541)
    (by decide : 72810541 ≤ 72876077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72745005 72876077).card = 518 := join_1_0

end S034C11
end Sude.GeneratedTwinScan
