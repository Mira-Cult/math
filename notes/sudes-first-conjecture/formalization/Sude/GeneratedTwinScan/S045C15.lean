import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96337965 96370733 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96337965 96370733).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96337965 96370733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96370733 96403501 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96370733 96403501).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96370733 96403501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96403501 96436269 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96403501 96436269).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96403501 96436269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96436269 96469037 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96436269 96469037).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96436269 96469037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96337965 96403501).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 96337965 ≤ 96370733)
    (by decide : 96370733 ≤ 96403501) block0 block1

theorem join_0_1 : (twinPrimeSegment 96403501 96469037).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 96403501 ≤ 96436269)
    (by decide : 96436269 ≤ 96469037) block2 block3

theorem join_1_0 : (twinPrimeSegment 96337965 96469037).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 96337965 ≤ 96403501)
    (by decide : 96403501 ≤ 96469037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96337965 96469037).card = 532 := join_1_0

end S045C15
end Sude.GeneratedTwinScan
