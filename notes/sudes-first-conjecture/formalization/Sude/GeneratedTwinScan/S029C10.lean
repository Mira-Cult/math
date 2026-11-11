import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62128173 62160941 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62128173 62160941).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62128173 62160941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62160941 62193709 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62160941 62193709).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62160941 62193709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62193709 62226477 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62193709 62226477).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62193709 62226477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62226477 62259245 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62226477 62259245).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62226477 62259245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62128173 62193709).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 62128173 ≤ 62160941)
    (by decide : 62160941 ≤ 62193709) block0 block1

theorem join_0_1 : (twinPrimeSegment 62193709 62259245).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 62193709 ≤ 62226477)
    (by decide : 62226477 ≤ 62259245) block2 block3

theorem join_1_0 : (twinPrimeSegment 62128173 62259245).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 62128173 ≤ 62193709)
    (by decide : 62193709 ≤ 62259245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62128173 62259245).card = 523 := join_1_0

end S029C10
end Sude.GeneratedTwinScan
