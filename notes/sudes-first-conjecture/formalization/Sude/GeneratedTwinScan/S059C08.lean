import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124780589 124813357 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124780589 124813357).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124780589 124813357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124813357 124846125 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124813357 124846125).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124813357 124846125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124846125 124878893 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124846125 124878893).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124846125 124878893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124878893 124911661 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124878893 124911661).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124878893 124911661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124780589 124846125).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 124780589 ≤ 124813357)
    (by decide : 124813357 ≤ 124846125) block0 block1

theorem join_0_1 : (twinPrimeSegment 124846125 124911661).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 124846125 ≤ 124878893)
    (by decide : 124878893 ≤ 124911661) block2 block3

theorem join_1_0 : (twinPrimeSegment 124780589 124911661).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 124780589 ≤ 124846125)
    (by decide : 124846125 ≤ 124911661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124780589 124911661).card = 501 := join_1_0

end S059C08
end Sude.GeneratedTwinScan
