import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59244589 59277357 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59244589 59277357).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59244589 59277357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59277357 59310125 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59277357 59310125).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59277357 59310125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59310125 59342893 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59310125 59342893).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59310125 59342893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59342893 59375661 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59342893 59375661).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59342893 59375661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59244589 59310125).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 59244589 ≤ 59277357)
    (by decide : 59277357 ≤ 59310125) block0 block1

theorem join_0_1 : (twinPrimeSegment 59310125 59375661).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 59310125 ≤ 59342893)
    (by decide : 59342893 ≤ 59375661) block2 block3

theorem join_1_0 : (twinPrimeSegment 59244589 59375661).card = 555 := by
  simpa using combineTwinPrimeSegments (by decide : 59244589 ≤ 59310125)
    (by decide : 59310125 ≤ 59375661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59244589 59375661).card = 555 := join_1_0

end S028C04
end Sude.GeneratedTwinScan
