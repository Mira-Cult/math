import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133693485 133726253 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133693485 133726253).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133693485 133726253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133726253 133759021 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133726253 133759021).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133726253 133759021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133759021 133791789 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133759021 133791789).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133759021 133791789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133791789 133824557 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133791789 133824557).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133791789 133824557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133693485 133759021).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 133693485 ≤ 133726253)
    (by decide : 133726253 ≤ 133759021) block0 block1

theorem join_0_1 : (twinPrimeSegment 133759021 133824557).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 133759021 ≤ 133791789)
    (by decide : 133791789 ≤ 133824557) block2 block3

theorem join_1_0 : (twinPrimeSegment 133693485 133824557).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 133693485 ≤ 133759021)
    (by decide : 133759021 ≤ 133824557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133693485 133824557).card = 478 := join_1_0

end S063C12
end Sude.GeneratedTwinScan
