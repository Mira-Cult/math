import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59506733 59539501 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59506733 59539501).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59506733 59539501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59539501 59572269 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59539501 59572269).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59539501 59572269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59572269 59605037 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59572269 59605037).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59572269 59605037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59605037 59637805 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59605037 59637805).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59605037 59637805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59506733 59572269).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 59506733 ≤ 59539501)
    (by decide : 59539501 ≤ 59572269) block0 block1

theorem join_0_1 : (twinPrimeSegment 59572269 59637805).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 59572269 ≤ 59605037)
    (by decide : 59605037 ≤ 59637805) block2 block3

theorem join_1_0 : (twinPrimeSegment 59506733 59637805).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 59506733 ≤ 59572269)
    (by decide : 59572269 ≤ 59637805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59506733 59637805).card = 543 := join_1_0

end S028C06
end Sude.GeneratedTwinScan
