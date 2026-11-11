import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90964013 90996781 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90964013 90996781).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90964013 90996781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90996781 91029549 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90996781 91029549).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90996781 91029549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91029549 91062317 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 91029549 91062317).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91029549 91062317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 91062317 91095085 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 91062317 91095085).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 91062317 91095085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90964013 91029549).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 90964013 ≤ 90996781)
    (by decide : 90996781 ≤ 91029549) block0 block1

theorem join_0_1 : (twinPrimeSegment 91029549 91095085).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 91029549 ≤ 91062317)
    (by decide : 91062317 ≤ 91095085) block2 block3

theorem join_1_0 : (twinPrimeSegment 90964013 91095085).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 90964013 ≤ 91029549)
    (by decide : 91029549 ≤ 91095085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90964013 91095085).card = 525 := join_1_0

end S043C06
end Sude.GeneratedTwinScan
