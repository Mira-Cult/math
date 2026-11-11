import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92274733 92307501 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92274733 92307501).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92274733 92307501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92307501 92340269 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92307501 92340269).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92307501 92340269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92340269 92373037 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92340269 92373037).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92340269 92373037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92373037 92405805 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92373037 92405805).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92373037 92405805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92274733 92340269).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 92307501)
    (by decide : 92307501 ≤ 92340269) block0 block1

theorem join_0_1 : (twinPrimeSegment 92340269 92405805).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 92340269 ≤ 92373037)
    (by decide : 92373037 ≤ 92405805) block2 block3

theorem join_1_0 : (twinPrimeSegment 92274733 92405805).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 92340269)
    (by decide : 92340269 ≤ 92405805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92274733 92405805).card = 486 := join_1_0

end S044C00
end Sude.GeneratedTwinScan
