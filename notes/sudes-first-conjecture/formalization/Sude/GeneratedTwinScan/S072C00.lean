import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150994989 151027757 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150994989 151027757).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150994989 151027757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151027757 151060525 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151027757 151060525).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151027757 151060525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151060525 151093293 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151060525 151093293).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151060525 151093293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151093293 151126061 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151093293 151126061).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151093293 151126061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150994989 151060525).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 151027757)
    (by decide : 151027757 ≤ 151060525) block0 block1

theorem join_0_1 : (twinPrimeSegment 151060525 151126061).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 151060525 ≤ 151093293)
    (by decide : 151093293 ≤ 151126061) block2 block3

theorem join_1_0 : (twinPrimeSegment 150994989 151126061).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 151060525)
    (by decide : 151060525 ≤ 151126061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150994989 151126061).card = 480 := join_1_0

end S072C00
end Sude.GeneratedTwinScan
