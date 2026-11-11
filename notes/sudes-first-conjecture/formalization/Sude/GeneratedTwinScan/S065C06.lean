import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137101357 137134125 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137101357 137134125).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137101357 137134125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137134125 137166893 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137134125 137166893).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137134125 137166893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137166893 137199661 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137166893 137199661).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137166893 137199661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137199661 137232429 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137199661 137232429).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137199661 137232429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137101357 137166893).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 137101357 ≤ 137134125)
    (by decide : 137134125 ≤ 137166893) block0 block1

theorem join_0_1 : (twinPrimeSegment 137166893 137232429).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 137166893 ≤ 137199661)
    (by decide : 137199661 ≤ 137232429) block2 block3

theorem join_1_0 : (twinPrimeSegment 137101357 137232429).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 137101357 ≤ 137166893)
    (by decide : 137166893 ≤ 137232429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137101357 137232429).card = 497 := join_1_0

end S065C06
end Sude.GeneratedTwinScan
