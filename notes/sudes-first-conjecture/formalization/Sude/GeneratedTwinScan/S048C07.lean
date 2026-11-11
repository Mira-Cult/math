import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101580845 101613613 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101580845 101613613).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101580845 101613613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101613613 101646381 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101613613 101646381).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101613613 101646381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101646381 101679149 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101646381 101679149).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101646381 101679149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101679149 101711917 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101679149 101711917).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101679149 101711917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101580845 101646381).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 101580845 ≤ 101613613)
    (by decide : 101613613 ≤ 101646381) block0 block1

theorem join_0_1 : (twinPrimeSegment 101646381 101711917).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 101646381 ≤ 101679149)
    (by decide : 101679149 ≤ 101711917) block2 block3

theorem join_1_0 : (twinPrimeSegment 101580845 101711917).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 101580845 ≤ 101646381)
    (by decide : 101646381 ≤ 101711917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101580845 101711917).card = 508 := join_1_0

end S048C07
end Sude.GeneratedTwinScan
