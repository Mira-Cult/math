import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105775149 105807917 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105775149 105807917).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105775149 105807917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105807917 105840685 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105807917 105840685).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105807917 105840685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105840685 105873453 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105840685 105873453).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105840685 105873453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105873453 105906221 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105873453 105906221).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105873453 105906221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105775149 105840685).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 105775149 ≤ 105807917)
    (by decide : 105807917 ≤ 105840685) block0 block1

theorem join_0_1 : (twinPrimeSegment 105840685 105906221).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 105840685 ≤ 105873453)
    (by decide : 105873453 ≤ 105906221) block2 block3

theorem join_1_0 : (twinPrimeSegment 105775149 105906221).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 105775149 ≤ 105840685)
    (by decide : 105840685 ≤ 105906221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105775149 105906221).card = 502 := join_1_0

end S050C07
end Sude.GeneratedTwinScan
