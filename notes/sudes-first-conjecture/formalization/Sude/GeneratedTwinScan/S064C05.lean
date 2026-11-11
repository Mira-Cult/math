import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134873133 134905901 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134873133 134905901).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134873133 134905901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134905901 134938669 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134905901 134938669).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134905901 134938669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134938669 134971437 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134938669 134971437).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134938669 134971437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134971437 135004205 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134971437 135004205).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134971437 135004205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134873133 134938669).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 134873133 ≤ 134905901)
    (by decide : 134905901 ≤ 134938669) block0 block1

theorem join_0_1 : (twinPrimeSegment 134938669 135004205).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 134938669 ≤ 134971437)
    (by decide : 134971437 ≤ 135004205) block2 block3

theorem join_1_0 : (twinPrimeSegment 134873133 135004205).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 134873133 ≤ 134938669)
    (by decide : 134938669 ≤ 135004205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134873133 135004205).card = 484 := join_1_0

end S064C05
end Sude.GeneratedTwinScan
