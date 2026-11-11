import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78512173 78544941 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78512173 78544941).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78512173 78544941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78544941 78577709 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78544941 78577709).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78544941 78577709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78577709 78610477 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78577709 78610477).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78577709 78610477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78610477 78643245 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 78610477 78643245).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78610477 78643245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78512173 78577709).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 78512173 ≤ 78544941)
    (by decide : 78544941 ≤ 78577709) block0 block1

theorem join_0_1 : (twinPrimeSegment 78577709 78643245).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 78577709 ≤ 78610477)
    (by decide : 78610477 ≤ 78643245) block2 block3

theorem join_1_0 : (twinPrimeSegment 78512173 78643245).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 78512173 ≤ 78577709)
    (by decide : 78577709 ≤ 78643245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78512173 78643245).card = 542 := join_1_0

end S037C07
end Sude.GeneratedTwinScan
