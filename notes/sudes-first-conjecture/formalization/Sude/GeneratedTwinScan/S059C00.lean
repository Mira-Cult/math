import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123732013 123764781 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123732013 123764781).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123732013 123764781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123764781 123797549 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123764781 123797549).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123764781 123797549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123797549 123830317 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123797549 123830317).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123797549 123830317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123830317 123863085 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123830317 123863085).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123830317 123863085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123732013 123797549).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 123764781)
    (by decide : 123764781 ≤ 123797549) block0 block1

theorem join_0_1 : (twinPrimeSegment 123797549 123863085).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 123797549 ≤ 123830317)
    (by decide : 123830317 ≤ 123863085) block2 block3

theorem join_1_0 : (twinPrimeSegment 123732013 123863085).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 123732013 ≤ 123797549)
    (by decide : 123797549 ≤ 123863085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123732013 123863085).card = 520 := join_1_0

end S059C00
end Sude.GeneratedTwinScan
