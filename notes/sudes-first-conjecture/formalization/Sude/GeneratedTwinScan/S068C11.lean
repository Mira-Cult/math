import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144048173 144080941 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144048173 144080941).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144048173 144080941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144080941 144113709 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144080941 144113709).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144080941 144113709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144113709 144146477 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144113709 144146477).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144113709 144146477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144146477 144179245 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144146477 144179245).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144146477 144179245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144048173 144113709).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 144048173 ≤ 144080941)
    (by decide : 144080941 ≤ 144113709) block0 block1

theorem join_0_1 : (twinPrimeSegment 144113709 144179245).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 144113709 ≤ 144146477)
    (by decide : 144146477 ≤ 144179245) block2 block3

theorem join_1_0 : (twinPrimeSegment 144048173 144179245).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 144048173 ≤ 144113709)
    (by decide : 144113709 ≤ 144179245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144048173 144179245).card = 510 := join_1_0

end S068C11
end Sude.GeneratedTwinScan
