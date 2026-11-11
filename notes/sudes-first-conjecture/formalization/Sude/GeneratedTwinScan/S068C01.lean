import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142737453 142770221 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142737453 142770221).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142737453 142770221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142770221 142802989 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 142770221 142802989).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142770221 142802989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142802989 142835757 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 142802989 142835757).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142802989 142835757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142835757 142868525 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 142835757 142868525).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142835757 142868525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142737453 142802989).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 142737453 ≤ 142770221)
    (by decide : 142770221 ≤ 142802989) block0 block1

theorem join_0_1 : (twinPrimeSegment 142802989 142868525).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 142802989 ≤ 142835757)
    (by decide : 142835757 ≤ 142868525) block2 block3

theorem join_1_0 : (twinPrimeSegment 142737453 142868525).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 142737453 ≤ 142802989)
    (by decide : 142802989 ≤ 142868525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142737453 142868525).card = 470 := join_1_0

end S068C01
end Sude.GeneratedTwinScan
