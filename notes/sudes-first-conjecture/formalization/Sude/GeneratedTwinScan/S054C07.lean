import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114163757 114196525 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 114163757 114196525).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114163757 114196525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114196525 114229293 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 114196525 114229293).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114196525 114229293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114229293 114262061 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 114229293 114262061).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114229293 114262061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 114262061 114294829 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 114262061 114294829).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 114262061 114294829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 114163757 114229293).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 114163757 ≤ 114196525)
    (by decide : 114196525 ≤ 114229293) block0 block1

theorem join_0_1 : (twinPrimeSegment 114229293 114294829).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 114229293 ≤ 114262061)
    (by decide : 114262061 ≤ 114294829) block2 block3

theorem join_1_0 : (twinPrimeSegment 114163757 114294829).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 114163757 ≤ 114229293)
    (by decide : 114229293 ≤ 114294829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 114163757 114294829).card = 480 := join_1_0

end S054C07
end Sude.GeneratedTwinScan
