import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114425901 114458669 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114425901 114458669).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114425901 114458669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114458669 114491437 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114458669 114491437).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114458669 114491437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114491437 114524205 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114491437 114524205).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114491437 114524205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114524205 114556973 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114524205 114556973).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114524205 114556973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114425901 114491437).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 114425901 ≤ 114458669)
    (by decide : 114458669 ≤ 114491437) block0 block1

theorem join_0_1 : (twinPrimeSegment 114491437 114556973).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 114491437 ≤ 114524205)
    (by decide : 114524205 ≤ 114556973) block2 block3

theorem join_1_0 : (twinPrimeSegment 114425901 114556973).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 114425901 ≤ 114491437)
    (by decide : 114491437 ≤ 114556973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114425901 114556973).card = 490 := join_1_0

end S054C09
end Sude.GeneratedTwinScan
