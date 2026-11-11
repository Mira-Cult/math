import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104988717 105021485 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104988717 105021485).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104988717 105021485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105021485 105054253 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105021485 105054253).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105021485 105054253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105054253 105087021 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105054253 105087021).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105054253 105087021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105087021 105119789 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105087021 105119789).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105087021 105119789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104988717 105054253).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 104988717 ≤ 105021485)
    (by decide : 105021485 ≤ 105054253) block0 block1

theorem join_0_1 : (twinPrimeSegment 105054253 105119789).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 105054253 ≤ 105087021)
    (by decide : 105087021 ≤ 105119789) block2 block3

theorem join_1_0 : (twinPrimeSegment 104988717 105119789).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 104988717 ≤ 105054253)
    (by decide : 105054253 ≤ 105119789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104988717 105119789).card = 533 := join_1_0

end S050C01
end Sude.GeneratedTwinScan
