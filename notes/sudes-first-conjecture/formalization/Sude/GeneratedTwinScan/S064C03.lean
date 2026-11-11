import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134610989 134643757 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134610989 134643757).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134610989 134643757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134643757 134676525 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134643757 134676525).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134643757 134676525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134676525 134709293 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134676525 134709293).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134676525 134709293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134709293 134742061 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134709293 134742061).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134709293 134742061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134610989 134676525).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 134610989 ≤ 134643757)
    (by decide : 134643757 ≤ 134676525) block0 block1

theorem join_0_1 : (twinPrimeSegment 134676525 134742061).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 134676525 ≤ 134709293)
    (by decide : 134709293 ≤ 134742061) block2 block3

theorem join_1_0 : (twinPrimeSegment 134610989 134742061).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 134610989 ≤ 134676525)
    (by decide : 134676525 ≤ 134742061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134610989 134742061).card = 490 := join_1_0

end S064C03
end Sude.GeneratedTwinScan
