import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105119789 105152557 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105119789 105152557).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105119789 105152557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105152557 105185325 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105152557 105185325).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105152557 105185325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105185325 105218093 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105185325 105218093).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105185325 105218093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105218093 105250861 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105218093 105250861).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105218093 105250861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105119789 105185325).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 105119789 ≤ 105152557)
    (by decide : 105152557 ≤ 105185325) block0 block1

theorem join_0_1 : (twinPrimeSegment 105185325 105250861).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 105185325 ≤ 105218093)
    (by decide : 105218093 ≤ 105250861) block2 block3

theorem join_1_0 : (twinPrimeSegment 105119789 105250861).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 105119789 ≤ 105185325)
    (by decide : 105185325 ≤ 105250861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105119789 105250861).card = 520 := join_1_0

end S050C02
end Sude.GeneratedTwinScan
