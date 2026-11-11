import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126091309 126124077 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126091309 126124077).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126091309 126124077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126124077 126156845 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126124077 126156845).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126124077 126156845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126156845 126189613 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126156845 126189613).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126156845 126189613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126189613 126222381 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126189613 126222381).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126189613 126222381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126091309 126156845).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 126091309 ≤ 126124077)
    (by decide : 126124077 ≤ 126156845) block0 block1

theorem join_0_1 : (twinPrimeSegment 126156845 126222381).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 126156845 ≤ 126189613)
    (by decide : 126189613 ≤ 126222381) block2 block3

theorem join_1_0 : (twinPrimeSegment 126091309 126222381).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 126091309 ≤ 126156845)
    (by decide : 126156845 ≤ 126222381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126091309 126222381).card = 511 := join_1_0

end S060C02
end Sude.GeneratedTwinScan
