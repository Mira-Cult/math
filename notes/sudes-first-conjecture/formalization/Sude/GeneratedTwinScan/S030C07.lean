import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63832109 63864877 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63832109 63864877).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63832109 63864877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63864877 63897645 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63864877 63897645).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63864877 63897645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63897645 63930413 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63897645 63930413).card = 156 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63897645 63930413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63930413 63963181 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63930413 63963181).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63930413 63963181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63832109 63897645).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 63832109 ≤ 63864877)
    (by decide : 63864877 ≤ 63897645) block0 block1

theorem join_0_1 : (twinPrimeSegment 63897645 63963181).card = 296 := by
  simpa using combineTwinPrimeSegments (by decide : 63897645 ≤ 63930413)
    (by decide : 63930413 ≤ 63963181) block2 block3

theorem join_1_0 : (twinPrimeSegment 63832109 63963181).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 63832109 ≤ 63897645)
    (by decide : 63897645 ≤ 63963181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63832109 63963181).card = 550 := join_1_0

end S030C07
end Sude.GeneratedTwinScan
