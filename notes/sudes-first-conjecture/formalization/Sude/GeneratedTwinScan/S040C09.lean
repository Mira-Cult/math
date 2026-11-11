import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85065773 85098541 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85065773 85098541).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85065773 85098541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85098541 85131309 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85098541 85131309).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85098541 85131309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85131309 85164077 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85131309 85164077).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85131309 85164077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85164077 85196845 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85164077 85196845).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85164077 85196845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85065773 85131309).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 85065773 ≤ 85098541)
    (by decide : 85098541 ≤ 85131309) block0 block1

theorem join_0_1 : (twinPrimeSegment 85131309 85196845).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 85131309 ≤ 85164077)
    (by decide : 85164077 ≤ 85196845) block2 block3

theorem join_1_0 : (twinPrimeSegment 85065773 85196845).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 85065773 ≤ 85131309)
    (by decide : 85131309 ≤ 85196845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85065773 85196845).card = 516 := join_1_0

end S040C09
end Sude.GeneratedTwinScan
