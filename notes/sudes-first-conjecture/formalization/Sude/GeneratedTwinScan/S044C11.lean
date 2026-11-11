import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93716525 93749293 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 93716525 93749293).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93716525 93749293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93749293 93782061 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 93749293 93782061).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93749293 93782061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93782061 93814829 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 93782061 93814829).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93782061 93814829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93814829 93847597 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 93814829 93847597).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93814829 93847597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 93716525 93782061).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 93716525 ≤ 93749293)
    (by decide : 93749293 ≤ 93782061) block0 block1

theorem join_0_1 : (twinPrimeSegment 93782061 93847597).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 93782061 ≤ 93814829)
    (by decide : 93814829 ≤ 93847597) block2 block3

theorem join_1_0 : (twinPrimeSegment 93716525 93847597).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 93716525 ≤ 93782061)
    (by decide : 93782061 ≤ 93847597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 93716525 93847597).card = 479 := join_1_0

end S044C11
end Sude.GeneratedTwinScan
