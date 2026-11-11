import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137232429 137265197 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137232429 137265197).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137232429 137265197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137265197 137297965 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137265197 137297965).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137265197 137297965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137297965 137330733 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137297965 137330733).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137297965 137330733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137330733 137363501 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137330733 137363501).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137330733 137363501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137232429 137297965).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 137232429 ≤ 137265197)
    (by decide : 137265197 ≤ 137297965) block0 block1

theorem join_0_1 : (twinPrimeSegment 137297965 137363501).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 137297965 ≤ 137330733)
    (by decide : 137330733 ≤ 137363501) block2 block3

theorem join_1_0 : (twinPrimeSegment 137232429 137363501).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 137232429 ≤ 137297965)
    (by decide : 137297965 ≤ 137363501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137232429 137363501).card = 489 := join_1_0

end S065C07
end Sude.GeneratedTwinScan
