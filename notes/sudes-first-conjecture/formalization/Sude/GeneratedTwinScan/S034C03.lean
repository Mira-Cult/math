import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71696429 71729197 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71696429 71729197).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71696429 71729197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71729197 71761965 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71729197 71761965).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71729197 71761965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71761965 71794733 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71761965 71794733).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71761965 71794733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71794733 71827501 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71794733 71827501).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71794733 71827501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71696429 71761965).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 71696429 ≤ 71729197)
    (by decide : 71729197 ≤ 71761965) block0 block1

theorem join_0_1 : (twinPrimeSegment 71761965 71827501).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 71761965 ≤ 71794733)
    (by decide : 71794733 ≤ 71827501) block2 block3

theorem join_1_0 : (twinPrimeSegment 71696429 71827501).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 71696429 ≤ 71761965)
    (by decide : 71761965 ≤ 71827501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71696429 71827501).card = 468 := join_1_0

end S034C03
end Sude.GeneratedTwinScan
