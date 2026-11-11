import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73793581 73826349 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73793581 73826349).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73793581 73826349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73826349 73859117 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73826349 73859117).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73826349 73859117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73859117 73891885 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73859117 73891885).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73859117 73891885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73891885 73924653 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73891885 73924653).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73891885 73924653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73793581 73859117).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 73793581 ≤ 73826349)
    (by decide : 73826349 ≤ 73859117) block0 block1

theorem join_0_1 : (twinPrimeSegment 73859117 73924653).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 73859117 ≤ 73891885)
    (by decide : 73891885 ≤ 73924653) block2 block3

theorem join_1_0 : (twinPrimeSegment 73793581 73924653).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 73793581 ≤ 73859117)
    (by decide : 73859117 ≤ 73924653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73793581 73924653).card = 553 := join_1_0

end S035C03
end Sude.GeneratedTwinScan
