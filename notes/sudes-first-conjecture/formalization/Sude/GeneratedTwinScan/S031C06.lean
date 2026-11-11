import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65798189 65830957 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65798189 65830957).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65798189 65830957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65830957 65863725 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65830957 65863725).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65830957 65863725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65863725 65896493 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65863725 65896493).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65863725 65896493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65896493 65929261 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65896493 65929261).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65896493 65929261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65798189 65863725).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 65798189 ≤ 65830957)
    (by decide : 65830957 ≤ 65863725) block0 block1

theorem join_0_1 : (twinPrimeSegment 65863725 65929261).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 65863725 ≤ 65896493)
    (by decide : 65896493 ≤ 65929261) block2 block3

theorem join_1_0 : (twinPrimeSegment 65798189 65929261).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 65798189 ≤ 65863725)
    (by decide : 65863725 ≤ 65929261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65798189 65929261).card = 516 := join_1_0

end S031C06
end Sude.GeneratedTwinScan
