import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128188461 128221229 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128188461 128221229).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128188461 128221229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128221229 128253997 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128221229 128253997).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128221229 128253997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128253997 128286765 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128253997 128286765).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128253997 128286765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128286765 128319533 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128286765 128319533).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128286765 128319533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128188461 128253997).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 128188461 ≤ 128221229)
    (by decide : 128221229 ≤ 128253997) block0 block1

theorem join_0_1 : (twinPrimeSegment 128253997 128319533).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 128253997 ≤ 128286765)
    (by decide : 128286765 ≤ 128319533) block2 block3

theorem join_1_0 : (twinPrimeSegment 128188461 128319533).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 128188461 ≤ 128253997)
    (by decide : 128253997 ≤ 128319533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128188461 128319533).card = 506 := join_1_0

end S061C02
end Sude.GeneratedTwinScan
