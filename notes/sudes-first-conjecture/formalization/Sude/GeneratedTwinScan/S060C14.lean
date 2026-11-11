import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127664173 127696941 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127664173 127696941).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127664173 127696941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127696941 127729709 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127696941 127729709).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127696941 127729709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127729709 127762477 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127729709 127762477).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127729709 127762477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127762477 127795245 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127762477 127795245).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127762477 127795245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127664173 127729709).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 127664173 ≤ 127696941)
    (by decide : 127696941 ≤ 127729709) block0 block1

theorem join_0_1 : (twinPrimeSegment 127729709 127795245).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 127729709 ≤ 127762477)
    (by decide : 127762477 ≤ 127795245) block2 block3

theorem join_1_0 : (twinPrimeSegment 127664173 127795245).card = 531 := by
  simpa using combineTwinPrimeSegments (by decide : 127664173 ≤ 127729709)
    (by decide : 127729709 ≤ 127795245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127664173 127795245).card = 531 := join_1_0

end S060C14
end Sude.GeneratedTwinScan
