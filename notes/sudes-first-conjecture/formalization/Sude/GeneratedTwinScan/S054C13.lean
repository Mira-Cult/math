import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114950189 114982957 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114950189 114982957).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114950189 114982957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114982957 115015725 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114982957 115015725).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114982957 115015725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115015725 115048493 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115015725 115048493).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115015725 115048493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115048493 115081261 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115048493 115081261).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115048493 115081261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114950189 115015725).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 114950189 ≤ 114982957)
    (by decide : 114982957 ≤ 115015725) block0 block1

theorem join_0_1 : (twinPrimeSegment 115015725 115081261).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 115015725 ≤ 115048493)
    (by decide : 115048493 ≤ 115081261) block2 block3

theorem join_1_0 : (twinPrimeSegment 114950189 115081261).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 114950189 ≤ 115015725)
    (by decide : 115015725 ≤ 115081261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114950189 115081261).card = 544 := join_1_0

end S054C13
end Sude.GeneratedTwinScan
