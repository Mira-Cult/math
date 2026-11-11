import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144572461 144605229 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144572461 144605229).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144572461 144605229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144605229 144637997 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144605229 144637997).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144605229 144637997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144637997 144670765 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144637997 144670765).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144637997 144670765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144670765 144703533 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144670765 144703533).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144670765 144703533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144572461 144637997).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 144572461 ≤ 144605229)
    (by decide : 144605229 ≤ 144637997) block0 block1

theorem join_0_1 : (twinPrimeSegment 144637997 144703533).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 144637997 ≤ 144670765)
    (by decide : 144670765 ≤ 144703533) block2 block3

theorem join_1_0 : (twinPrimeSegment 144572461 144703533).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 144572461 ≤ 144637997)
    (by decide : 144637997 ≤ 144703533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144572461 144703533).card = 482 := join_1_0

end S068C15
end Sude.GeneratedTwinScan
