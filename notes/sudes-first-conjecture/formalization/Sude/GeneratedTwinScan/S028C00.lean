import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58720301 58753069 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58720301 58753069).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58720301 58753069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58753069 58785837 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58753069 58785837).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58753069 58785837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58785837 58818605 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58785837 58818605).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58785837 58818605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 58818605 58851373 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58818605 58851373).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 58818605 58851373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 58720301 58785837).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 58753069)
    (by decide : 58753069 ≤ 58785837) block0 block1

theorem join_0_1 : (twinPrimeSegment 58785837 58851373).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 58785837 ≤ 58818605)
    (by decide : 58818605 ≤ 58851373) block2 block3

theorem join_1_0 : (twinPrimeSegment 58720301 58851373).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 58785837)
    (by decide : 58785837 ≤ 58851373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58720301 58851373).card = 549 := join_1_0

end S028C00
end Sude.GeneratedTwinScan
