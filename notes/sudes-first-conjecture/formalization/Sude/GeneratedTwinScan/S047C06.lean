import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99352621 99385389 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99352621 99385389).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99352621 99385389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99385389 99418157 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99385389 99418157).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99385389 99418157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99418157 99450925 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99418157 99450925).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99418157 99450925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99450925 99483693 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99450925 99483693).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99450925 99483693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99352621 99418157).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 99352621 ≤ 99385389)
    (by decide : 99385389 ≤ 99418157) block0 block1

theorem join_0_1 : (twinPrimeSegment 99418157 99483693).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 99418157 ≤ 99450925)
    (by decide : 99450925 ≤ 99483693) block2 block3

theorem join_1_0 : (twinPrimeSegment 99352621 99483693).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 99352621 ≤ 99418157)
    (by decide : 99418157 ≤ 99483693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99352621 99483693).card = 524 := join_1_0

end S047C06
end Sude.GeneratedTwinScan
