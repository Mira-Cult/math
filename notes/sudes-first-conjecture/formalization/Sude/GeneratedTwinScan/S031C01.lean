import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65142829 65175597 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65142829 65175597).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65142829 65175597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65175597 65208365 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65175597 65208365).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65175597 65208365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65208365 65241133 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65208365 65241133).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65208365 65241133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65241133 65273901 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65241133 65273901).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65241133 65273901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65142829 65208365).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 65142829 ≤ 65175597)
    (by decide : 65175597 ≤ 65208365) block0 block1

theorem join_0_1 : (twinPrimeSegment 65208365 65273901).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 65208365 ≤ 65241133)
    (by decide : 65241133 ≤ 65273901) block2 block3

theorem join_1_0 : (twinPrimeSegment 65142829 65273901).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 65142829 ≤ 65208365)
    (by decide : 65208365 ≤ 65273901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65142829 65273901).card = 540 := join_1_0

end S031C01
end Sude.GeneratedTwinScan
