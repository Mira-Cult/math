import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87293997 87326765 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87293997 87326765).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87293997 87326765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87326765 87359533 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87326765 87359533).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87326765 87359533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87359533 87392301 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87359533 87392301).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87359533 87392301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87392301 87425069 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87392301 87425069).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87392301 87425069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87293997 87359533).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 87293997 ≤ 87326765)
    (by decide : 87326765 ≤ 87359533) block0 block1

theorem join_0_1 : (twinPrimeSegment 87359533 87425069).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 87359533 ≤ 87392301)
    (by decide : 87392301 ≤ 87425069) block2 block3

theorem join_1_0 : (twinPrimeSegment 87293997 87425069).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 87293997 ≤ 87359533)
    (by decide : 87359533 ≤ 87425069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87293997 87425069).card = 496 := join_1_0

end S041C10
end Sude.GeneratedTwinScan
