import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59375661 59408429 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59375661 59408429).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59375661 59408429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59408429 59441197 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59408429 59441197).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59408429 59441197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59441197 59473965 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59441197 59473965).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59441197 59473965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59473965 59506733 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59473965 59506733).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59473965 59506733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59375661 59441197).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 59375661 ≤ 59408429)
    (by decide : 59408429 ≤ 59441197) block0 block1

theorem join_0_1 : (twinPrimeSegment 59441197 59506733).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 59441197 ≤ 59473965)
    (by decide : 59473965 ≤ 59506733) block2 block3

theorem join_1_0 : (twinPrimeSegment 59375661 59506733).card = 531 := by
  simpa using combineTwinPrimeSegments (by decide : 59375661 ≤ 59441197)
    (by decide : 59441197 ≤ 59506733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59375661 59506733).card = 531 := join_1_0

end S028C05
end Sude.GeneratedTwinScan
