import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139329581 139362349 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139329581 139362349).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139329581 139362349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139362349 139395117 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139362349 139395117).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139362349 139395117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139395117 139427885 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139395117 139427885).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139395117 139427885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139427885 139460653 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139427885 139460653).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139427885 139460653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139329581 139395117).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 139329581 ≤ 139362349)
    (by decide : 139362349 ≤ 139395117) block0 block1

theorem join_0_1 : (twinPrimeSegment 139395117 139460653).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 139395117 ≤ 139427885)
    (by decide : 139427885 ≤ 139460653) block2 block3

theorem join_1_0 : (twinPrimeSegment 139329581 139460653).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 139329581 ≤ 139395117)
    (by decide : 139395117 ≤ 139460653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139329581 139460653).card = 503 := join_1_0

end S066C07
end Sude.GeneratedTwinScan
