import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106823725 106856493 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106823725 106856493).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106823725 106856493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106856493 106889261 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106856493 106889261).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106856493 106889261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106889261 106922029 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106889261 106922029).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106889261 106922029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106922029 106954797 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106922029 106954797).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106922029 106954797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106823725 106889261).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 106823725 ≤ 106856493)
    (by decide : 106856493 ≤ 106889261) block0 block1

theorem join_0_1 : (twinPrimeSegment 106889261 106954797).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 106889261 ≤ 106922029)
    (by decide : 106922029 ≤ 106954797) block2 block3

theorem join_1_0 : (twinPrimeSegment 106823725 106954797).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 106823725 ≤ 106889261)
    (by decide : 106889261 ≤ 106954797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106823725 106954797).card = 462 := join_1_0

end S050C15
end Sude.GeneratedTwinScan
