import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94371885 94404653 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94371885 94404653).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94371885 94404653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94404653 94437421 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94404653 94437421).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94404653 94437421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94437421 94470189 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94437421 94470189).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94437421 94470189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94470189 94502957 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94470189 94502957).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94470189 94502957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94371885 94437421).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 94404653)
    (by decide : 94404653 ≤ 94437421) block0 block1

theorem join_0_1 : (twinPrimeSegment 94437421 94502957).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 94437421 ≤ 94470189)
    (by decide : 94470189 ≤ 94502957) block2 block3

theorem join_1_0 : (twinPrimeSegment 94371885 94502957).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 94371885 ≤ 94437421)
    (by decide : 94437421 ≤ 94502957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94371885 94502957).card = 508 := join_1_0

end S045C00
end Sude.GeneratedTwinScan
