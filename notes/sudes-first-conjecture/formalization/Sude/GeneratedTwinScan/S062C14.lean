import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131858477 131891245 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131858477 131891245).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131858477 131891245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131891245 131924013 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131891245 131924013).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131891245 131924013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131924013 131956781 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131924013 131956781).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131924013 131956781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131956781 131989549 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131956781 131989549).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131956781 131989549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131858477 131924013).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 131858477 ≤ 131891245)
    (by decide : 131891245 ≤ 131924013) block0 block1

theorem join_0_1 : (twinPrimeSegment 131924013 131989549).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 131924013 ≤ 131956781)
    (by decide : 131956781 ≤ 131989549) block2 block3

theorem join_1_0 : (twinPrimeSegment 131858477 131989549).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 131858477 ≤ 131924013)
    (by decide : 131924013 ≤ 131989549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131858477 131989549).card = 512 := join_1_0

end S062C14
end Sude.GeneratedTwinScan
