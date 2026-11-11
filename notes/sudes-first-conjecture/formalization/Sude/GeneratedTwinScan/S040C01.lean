import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84017197 84049965 = 157 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84017197 84049965).card = 157 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84017197 84049965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84049965 84082733 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84049965 84082733).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84049965 84082733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84082733 84115501 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84082733 84115501).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84082733 84115501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84115501 84148269 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84115501 84148269).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84115501 84148269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84017197 84082733).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 84017197 ≤ 84049965)
    (by decide : 84049965 ≤ 84082733) block0 block1

theorem join_0_1 : (twinPrimeSegment 84082733 84148269).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 84082733 ≤ 84115501)
    (by decide : 84115501 ≤ 84148269) block2 block3

theorem join_1_0 : (twinPrimeSegment 84017197 84148269).card = 542 := by
  simpa using combineTwinPrimeSegments (by decide : 84017197 ≤ 84082733)
    (by decide : 84082733 ≤ 84148269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84017197 84148269).card = 542 := join_1_0

end S040C01
end Sude.GeneratedTwinScan
