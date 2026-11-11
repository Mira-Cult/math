import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111280173 111312941 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111280173 111312941).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111280173 111312941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111312941 111345709 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111312941 111345709).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111312941 111345709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111345709 111378477 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111345709 111378477).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111345709 111378477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111378477 111411245 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111378477 111411245).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111378477 111411245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111280173 111345709).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 111280173 ≤ 111312941)
    (by decide : 111312941 ≤ 111345709) block0 block1

theorem join_0_1 : (twinPrimeSegment 111345709 111411245).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 111345709 ≤ 111378477)
    (by decide : 111378477 ≤ 111411245) block2 block3

theorem join_1_0 : (twinPrimeSegment 111280173 111411245).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 111280173 ≤ 111345709)
    (by decide : 111345709 ≤ 111411245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111280173 111411245).card = 495 := join_1_0

end S053C01
end Sude.GeneratedTwinScan
