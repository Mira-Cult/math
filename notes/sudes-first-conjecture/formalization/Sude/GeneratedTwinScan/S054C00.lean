import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113246253 113279021 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 113246253 113279021).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113246253 113279021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113279021 113311789 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113279021 113311789).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113279021 113311789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113311789 113344557 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113311789 113344557).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113311789 113344557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113344557 113377325 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113344557 113377325).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113344557 113377325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 113246253 113311789).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 113279021)
    (by decide : 113279021 ≤ 113311789) block0 block1

theorem join_0_1 : (twinPrimeSegment 113311789 113377325).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 113311789 ≤ 113344557)
    (by decide : 113344557 ≤ 113377325) block2 block3

theorem join_1_0 : (twinPrimeSegment 113246253 113377325).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 113311789)
    (by decide : 113311789 ≤ 113377325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 113246253 113377325).card = 491 := join_1_0

end S054C00
end Sude.GeneratedTwinScan
