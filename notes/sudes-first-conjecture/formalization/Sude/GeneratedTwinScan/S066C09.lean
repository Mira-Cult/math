import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139591725 139624493 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139591725 139624493).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139591725 139624493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139624493 139657261 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139624493 139657261).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139624493 139657261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139657261 139690029 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139657261 139690029).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139657261 139690029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139690029 139722797 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139690029 139722797).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139690029 139722797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139591725 139657261).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 139591725 ≤ 139624493)
    (by decide : 139624493 ≤ 139657261) block0 block1

theorem join_0_1 : (twinPrimeSegment 139657261 139722797).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 139657261 ≤ 139690029)
    (by decide : 139690029 ≤ 139722797) block2 block3

theorem join_1_0 : (twinPrimeSegment 139591725 139722797).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 139591725 ≤ 139657261)
    (by decide : 139657261 ≤ 139722797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139591725 139722797).card = 509 := join_1_0

end S066C09
end Sude.GeneratedTwinScan
