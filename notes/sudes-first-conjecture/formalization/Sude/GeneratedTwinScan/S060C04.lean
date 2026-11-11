import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126353453 126386221 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126353453 126386221).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126353453 126386221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126386221 126418989 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126386221 126418989).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126386221 126418989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126418989 126451757 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126418989 126451757).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126418989 126451757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126451757 126484525 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126451757 126484525).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126451757 126484525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126353453 126418989).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 126353453 ≤ 126386221)
    (by decide : 126386221 ≤ 126418989) block0 block1

theorem join_0_1 : (twinPrimeSegment 126418989 126484525).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 126418989 ≤ 126451757)
    (by decide : 126451757 ≤ 126484525) block2 block3

theorem join_1_0 : (twinPrimeSegment 126353453 126484525).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 126353453 ≤ 126418989)
    (by decide : 126418989 ≤ 126484525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126353453 126484525).card = 490 := join_1_0

end S060C04
end Sude.GeneratedTwinScan
