import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109707309 109740077 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109707309 109740077).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109707309 109740077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109740077 109772845 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109740077 109772845).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109740077 109772845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109772845 109805613 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109772845 109805613).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109772845 109805613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109805613 109838381 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109805613 109838381).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109805613 109838381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109707309 109772845).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 109707309 ≤ 109740077)
    (by decide : 109740077 ≤ 109772845) block0 block1

theorem join_0_1 : (twinPrimeSegment 109772845 109838381).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 109772845 ≤ 109805613)
    (by decide : 109805613 ≤ 109838381) block2 block3

theorem join_1_0 : (twinPrimeSegment 109707309 109838381).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 109707309 ≤ 109772845)
    (by decide : 109772845 ≤ 109838381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109707309 109838381).card = 493 := join_1_0

end S052C05
end Sude.GeneratedTwinScan
