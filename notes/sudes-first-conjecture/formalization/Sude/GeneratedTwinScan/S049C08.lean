import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103809069 103841837 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103809069 103841837).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103809069 103841837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103841837 103874605 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103841837 103874605).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103841837 103874605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103874605 103907373 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103874605 103907373).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103874605 103907373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103907373 103940141 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103907373 103940141).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103907373 103940141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103809069 103874605).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 103809069 ≤ 103841837)
    (by decide : 103841837 ≤ 103874605) block0 block1

theorem join_0_1 : (twinPrimeSegment 103874605 103940141).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 103874605 ≤ 103907373)
    (by decide : 103907373 ≤ 103940141) block2 block3

theorem join_1_0 : (twinPrimeSegment 103809069 103940141).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 103809069 ≤ 103874605)
    (by decide : 103874605 ≤ 103940141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103809069 103940141).card = 483 := join_1_0

end S049C08
end Sude.GeneratedTwinScan
