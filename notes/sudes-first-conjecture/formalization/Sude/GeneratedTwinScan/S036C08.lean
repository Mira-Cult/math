import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76546093 76578861 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76546093 76578861).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76546093 76578861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76578861 76611629 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76578861 76611629).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76578861 76611629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76611629 76644397 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76611629 76644397).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76611629 76644397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76644397 76677165 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76644397 76677165).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76644397 76677165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76546093 76611629).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 76546093 ≤ 76578861)
    (by decide : 76578861 ≤ 76611629) block0 block1

theorem join_0_1 : (twinPrimeSegment 76611629 76677165).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 76611629 ≤ 76644397)
    (by decide : 76644397 ≤ 76677165) block2 block3

theorem join_1_0 : (twinPrimeSegment 76546093 76677165).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 76546093 ≤ 76611629)
    (by decide : 76611629 ≤ 76677165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76546093 76677165).card = 520 := join_1_0

end S036C08
end Sude.GeneratedTwinScan
