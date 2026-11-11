import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119930925 119963693 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119930925 119963693).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119930925 119963693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119963693 119996461 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119963693 119996461).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119963693 119996461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119996461 120029229 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119996461 120029229).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119996461 120029229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120029229 120061997 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120029229 120061997).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120029229 120061997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119930925 119996461).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 119930925 ≤ 119963693)
    (by decide : 119963693 ≤ 119996461) block0 block1

theorem join_0_1 : (twinPrimeSegment 119996461 120061997).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 119996461 ≤ 120029229)
    (by decide : 120029229 ≤ 120061997) block2 block3

theorem join_1_0 : (twinPrimeSegment 119930925 120061997).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 119930925 ≤ 119996461)
    (by decide : 119996461 ≤ 120061997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119930925 120061997).card = 495 := join_1_0

end S057C03
end Sude.GeneratedTwinScan
