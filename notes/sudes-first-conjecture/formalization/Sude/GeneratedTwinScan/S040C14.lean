import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85721133 85753901 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85721133 85753901).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85721133 85753901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85753901 85786669 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85753901 85786669).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85753901 85786669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85786669 85819437 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85786669 85819437).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85786669 85819437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85819437 85852205 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85819437 85852205).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85819437 85852205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85721133 85786669).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 85721133 ≤ 85753901)
    (by decide : 85753901 ≤ 85786669) block0 block1

theorem join_0_1 : (twinPrimeSegment 85786669 85852205).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 85786669 ≤ 85819437)
    (by decide : 85819437 ≤ 85852205) block2 block3

theorem join_1_0 : (twinPrimeSegment 85721133 85852205).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 85721133 ≤ 85786669)
    (by decide : 85786669 ≤ 85852205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85721133 85852205).card = 505 := join_1_0

end S040C14
end Sude.GeneratedTwinScan
