import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82837549 82870317 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82837549 82870317).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82837549 82870317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82870317 82903085 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82870317 82903085).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82870317 82903085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82903085 82935853 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82903085 82935853).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82903085 82935853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82935853 82968621 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82935853 82968621).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82935853 82968621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82837549 82903085).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 82837549 ≤ 82870317)
    (by decide : 82870317 ≤ 82903085) block0 block1

theorem join_0_1 : (twinPrimeSegment 82903085 82968621).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 82903085 ≤ 82935853)
    (by decide : 82935853 ≤ 82968621) block2 block3

theorem join_1_0 : (twinPrimeSegment 82837549 82968621).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 82837549 ≤ 82903085)
    (by decide : 82903085 ≤ 82968621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82837549 82968621).card = 500 := join_1_0

end S039C08
end Sude.GeneratedTwinScan
