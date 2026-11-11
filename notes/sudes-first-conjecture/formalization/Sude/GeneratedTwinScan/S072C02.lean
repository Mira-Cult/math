import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151257133 151289901 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151257133 151289901).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151257133 151289901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151289901 151322669 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151289901 151322669).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151289901 151322669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151322669 151355437 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151322669 151355437).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151322669 151355437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151355437 151388205 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 151355437 151388205).card = 98 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151355437 151388205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151257133 151322669).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 151257133 ≤ 151289901)
    (by decide : 151289901 ≤ 151322669) block0 block1

theorem join_0_1 : (twinPrimeSegment 151322669 151388205).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 151322669 ≤ 151355437)
    (by decide : 151355437 ≤ 151388205) block2 block3

theorem join_1_0 : (twinPrimeSegment 151257133 151388205).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 151257133 ≤ 151322669)
    (by decide : 151322669 ≤ 151388205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151257133 151388205).card = 456 := join_1_0

end S072C02
end Sude.GeneratedTwinScan
