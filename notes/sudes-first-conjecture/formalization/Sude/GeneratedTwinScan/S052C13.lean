import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110755885 110788653 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110755885 110788653).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110755885 110788653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110788653 110821421 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110788653 110821421).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110788653 110821421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110821421 110854189 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110821421 110854189).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110821421 110854189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110854189 110886957 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110854189 110886957).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110854189 110886957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110755885 110821421).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 110755885 ≤ 110788653)
    (by decide : 110788653 ≤ 110821421) block0 block1

theorem join_0_1 : (twinPrimeSegment 110821421 110886957).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 110821421 ≤ 110854189)
    (by decide : 110854189 ≤ 110886957) block2 block3

theorem join_1_0 : (twinPrimeSegment 110755885 110886957).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 110755885 ≤ 110821421)
    (by decide : 110821421 ≤ 110886957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110755885 110886957).card = 477 := join_1_0

end S052C13
end Sude.GeneratedTwinScan
