import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63307821 63340589 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63307821 63340589).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63307821 63340589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63340589 63373357 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63340589 63373357).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63340589 63373357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63373357 63406125 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63373357 63406125).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63373357 63406125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63406125 63438893 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63406125 63438893).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63406125 63438893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63307821 63373357).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 63307821 ≤ 63340589)
    (by decide : 63340589 ≤ 63373357) block0 block1

theorem join_0_1 : (twinPrimeSegment 63373357 63438893).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 63373357 ≤ 63406125)
    (by decide : 63406125 ≤ 63438893) block2 block3

theorem join_1_0 : (twinPrimeSegment 63307821 63438893).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 63307821 ≤ 63373357)
    (by decide : 63373357 ≤ 63438893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63307821 63438893).card = 528 := join_1_0

end S030C03
end Sude.GeneratedTwinScan
