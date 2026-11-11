import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146276397 146309165 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146276397 146309165).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146276397 146309165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146309165 146341933 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146309165 146341933).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146309165 146341933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146341933 146374701 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146341933 146374701).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146341933 146374701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146374701 146407469 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146374701 146407469).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146374701 146407469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146276397 146341933).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 146276397 ≤ 146309165)
    (by decide : 146309165 ≤ 146341933) block0 block1

theorem join_0_1 : (twinPrimeSegment 146341933 146407469).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 146341933 ≤ 146374701)
    (by decide : 146374701 ≤ 146407469) block2 block3

theorem join_1_0 : (twinPrimeSegment 146276397 146407469).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 146276397 ≤ 146341933)
    (by decide : 146341933 ≤ 146407469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146276397 146407469).card = 504 := join_1_0

end S069C12
end Sude.GeneratedTwinScan
