import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137887789 137920557 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137887789 137920557).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137887789 137920557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137920557 137953325 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137920557 137953325).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137920557 137953325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137953325 137986093 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137953325 137986093).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137953325 137986093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137986093 138018861 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137986093 138018861).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137986093 138018861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137887789 137953325).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 137887789 ≤ 137920557)
    (by decide : 137920557 ≤ 137953325) block0 block1

theorem join_0_1 : (twinPrimeSegment 137953325 138018861).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 137953325 ≤ 137986093)
    (by decide : 137986093 ≤ 138018861) block2 block3

theorem join_1_0 : (twinPrimeSegment 137887789 138018861).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 137887789 ≤ 137953325)
    (by decide : 137953325 ≤ 138018861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137887789 138018861).card = 496 := join_1_0

end S065C12
end Sude.GeneratedTwinScan
