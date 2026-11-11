import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68419629 68452397 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68419629 68452397).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68419629 68452397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68452397 68485165 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68452397 68485165).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68452397 68485165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68485165 68517933 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68485165 68517933).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68485165 68517933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68517933 68550701 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68517933 68550701).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68517933 68550701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68419629 68485165).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 68419629 ≤ 68452397)
    (by decide : 68452397 ≤ 68485165) block0 block1

theorem join_0_1 : (twinPrimeSegment 68485165 68550701).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 68485165 ≤ 68517933)
    (by decide : 68517933 ≤ 68550701) block2 block3

theorem join_1_0 : (twinPrimeSegment 68419629 68550701).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 68419629 ≤ 68485165)
    (by decide : 68485165 ≤ 68550701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68419629 68550701).card = 532 := join_1_0

end S032C10
end Sude.GeneratedTwinScan
