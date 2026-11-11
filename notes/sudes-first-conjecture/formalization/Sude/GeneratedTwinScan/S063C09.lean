import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133300269 133333037 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133300269 133333037).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133300269 133333037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133333037 133365805 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133333037 133365805).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133333037 133365805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133365805 133398573 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133365805 133398573).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133365805 133398573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133398573 133431341 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133398573 133431341).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133398573 133431341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133300269 133365805).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 133300269 ≤ 133333037)
    (by decide : 133333037 ≤ 133365805) block0 block1

theorem join_0_1 : (twinPrimeSegment 133365805 133431341).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 133365805 ≤ 133398573)
    (by decide : 133398573 ≤ 133431341) block2 block3

theorem join_1_0 : (twinPrimeSegment 133300269 133431341).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 133300269 ≤ 133365805)
    (by decide : 133365805 ≤ 133431341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133300269 133431341).card = 513 := join_1_0

end S063C09
end Sude.GeneratedTwinScan
