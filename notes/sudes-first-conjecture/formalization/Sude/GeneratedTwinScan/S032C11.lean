import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68550701 68583469 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68550701 68583469).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68550701 68583469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68583469 68616237 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68583469 68616237).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68583469 68616237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68616237 68649005 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68616237 68649005).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68616237 68649005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68649005 68681773 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68649005 68681773).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68649005 68681773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68550701 68616237).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 68550701 ≤ 68583469)
    (by decide : 68583469 ≤ 68616237) block0 block1

theorem join_0_1 : (twinPrimeSegment 68616237 68681773).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 68616237 ≤ 68649005)
    (by decide : 68649005 ≤ 68681773) block2 block3

theorem join_1_0 : (twinPrimeSegment 68550701 68681773).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 68550701 ≤ 68616237)
    (by decide : 68616237 ≤ 68681773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68550701 68681773).card = 544 := join_1_0

end S032C11
end Sude.GeneratedTwinScan
