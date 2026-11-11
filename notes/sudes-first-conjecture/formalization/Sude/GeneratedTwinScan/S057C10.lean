import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120848429 120881197 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120848429 120881197).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120848429 120881197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120881197 120913965 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120881197 120913965).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120881197 120913965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120913965 120946733 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120913965 120946733).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120913965 120946733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120946733 120979501 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120946733 120979501).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120946733 120979501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120848429 120913965).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 120848429 ≤ 120881197)
    (by decide : 120881197 ≤ 120913965) block0 block1

theorem join_0_1 : (twinPrimeSegment 120913965 120979501).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 120913965 ≤ 120946733)
    (by decide : 120946733 ≤ 120979501) block2 block3

theorem join_1_0 : (twinPrimeSegment 120848429 120979501).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 120848429 ≤ 120913965)
    (by decide : 120913965 ≤ 120979501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120848429 120979501).card = 482 := join_1_0

end S057C10
end Sude.GeneratedTwinScan
