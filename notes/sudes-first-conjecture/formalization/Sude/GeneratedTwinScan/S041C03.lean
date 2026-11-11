import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86376493 86409261 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 86376493 86409261).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86376493 86409261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86409261 86442029 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 86409261 86442029).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86409261 86442029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86442029 86474797 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 86442029 86474797).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86442029 86474797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86474797 86507565 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 86474797 86507565).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86474797 86507565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 86376493 86442029).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 86376493 ≤ 86409261)
    (by decide : 86409261 ≤ 86442029) block0 block1

theorem join_0_1 : (twinPrimeSegment 86442029 86507565).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 86442029 ≤ 86474797)
    (by decide : 86474797 ≤ 86507565) block2 block3

theorem join_1_0 : (twinPrimeSegment 86376493 86507565).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 86376493 ≤ 86442029)
    (by decide : 86442029 ≤ 86507565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 86376493 86507565).card = 533 := join_1_0

end S041C03
end Sude.GeneratedTwinScan
