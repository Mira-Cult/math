import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107872301 107905069 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107872301 107905069).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107872301 107905069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107905069 107937837 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107905069 107937837).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107905069 107937837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107937837 107970605 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107937837 107970605).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107937837 107970605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107970605 108003373 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107970605 108003373).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107970605 108003373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107872301 107937837).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 107872301 ≤ 107905069)
    (by decide : 107905069 ≤ 107937837) block0 block1

theorem join_0_1 : (twinPrimeSegment 107937837 108003373).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 107937837 ≤ 107970605)
    (by decide : 107970605 ≤ 108003373) block2 block3

theorem join_1_0 : (twinPrimeSegment 107872301 108003373).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 107872301 ≤ 107937837)
    (by decide : 107937837 ≤ 108003373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107872301 108003373).card = 474 := join_1_0

end S051C07
end Sude.GeneratedTwinScan
