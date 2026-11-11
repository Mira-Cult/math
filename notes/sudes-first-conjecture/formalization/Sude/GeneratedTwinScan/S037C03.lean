import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77987885 78020653 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77987885 78020653).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77987885 78020653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78020653 78053421 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78020653 78053421).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78020653 78053421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78053421 78086189 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78053421 78086189).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78053421 78086189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78086189 78118957 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78086189 78118957).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78086189 78118957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77987885 78053421).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 77987885 ≤ 78020653)
    (by decide : 78020653 ≤ 78053421) block0 block1

theorem join_0_1 : (twinPrimeSegment 78053421 78118957).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 78053421 ≤ 78086189)
    (by decide : 78086189 ≤ 78118957) block2 block3

theorem join_1_0 : (twinPrimeSegment 77987885 78118957).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 77987885 ≤ 78053421)
    (by decide : 78053421 ≤ 78118957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77987885 78118957).card = 528 := join_1_0

end S037C03
end Sude.GeneratedTwinScan
