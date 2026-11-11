import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147849261 147882029 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147849261 147882029).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147849261 147882029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147882029 147914797 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147882029 147914797).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147882029 147914797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147914797 147947565 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147914797 147947565).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147914797 147947565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147947565 147980333 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147947565 147980333).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147947565 147980333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147849261 147914797).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 147849261 ≤ 147882029)
    (by decide : 147882029 ≤ 147914797) block0 block1

theorem join_0_1 : (twinPrimeSegment 147914797 147980333).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 147914797 ≤ 147947565)
    (by decide : 147947565 ≤ 147980333) block2 block3

theorem join_1_0 : (twinPrimeSegment 147849261 147980333).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 147849261 ≤ 147914797)
    (by decide : 147914797 ≤ 147980333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147849261 147980333).card = 476 := join_1_0

end S070C08
end Sude.GeneratedTwinScan
