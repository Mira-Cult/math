import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60948525 60981293 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60948525 60981293).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60948525 60981293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60981293 61014061 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60981293 61014061).card = 155 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60981293 61014061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61014061 61046829 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61014061 61046829).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61014061 61046829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61046829 61079597 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61046829 61079597).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61046829 61079597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60948525 61014061).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 60948525 ≤ 60981293)
    (by decide : 60981293 ≤ 61014061) block0 block1

theorem join_0_1 : (twinPrimeSegment 61014061 61079597).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 61014061 ≤ 61046829)
    (by decide : 61046829 ≤ 61079597) block2 block3

theorem join_1_0 : (twinPrimeSegment 60948525 61079597).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 60948525 ≤ 61014061)
    (by decide : 61014061 ≤ 61079597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60948525 61079597).card = 549 := join_1_0

end S029C01
end Sude.GeneratedTwinScan
