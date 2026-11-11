import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67502125 67534893 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67502125 67534893).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67502125 67534893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67534893 67567661 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67534893 67567661).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67534893 67567661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67567661 67600429 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67567661 67600429).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67567661 67600429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67600429 67633197 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67600429 67633197).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67600429 67633197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67502125 67567661).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 67502125 ≤ 67534893)
    (by decide : 67534893 ≤ 67567661) block0 block1

theorem join_0_1 : (twinPrimeSegment 67567661 67633197).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 67567661 ≤ 67600429)
    (by decide : 67600429 ≤ 67633197) block2 block3

theorem join_1_0 : (twinPrimeSegment 67502125 67633197).card = 552 := by
  simpa using combineTwinPrimeSegments (by decide : 67502125 ≤ 67567661)
    (by decide : 67567661 ≤ 67633197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67502125 67633197).card = 552 := join_1_0

end S032C03
end Sude.GeneratedTwinScan
