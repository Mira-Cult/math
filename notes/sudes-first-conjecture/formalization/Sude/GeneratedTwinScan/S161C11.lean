import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18415)) 339083309 339116077 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 339083309 339116077).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18415 339083309 339116077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18415)) 339116077 339148845 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 339116077 339148845).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18415 339116077 339148845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18416)) 339148845 339181613 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339148845 339181613).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18416 339148845 339181613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18417)) 339181613 339214381 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339181613 339214381).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18417 339181613 339214381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 339083309 339148845).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 339083309 ≤ 339116077)
    (by decide : 339116077 ≤ 339148845) block0 block1

theorem join_0_1 : (twinPrimeSegment 339148845 339214381).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 339148845 ≤ 339181613)
    (by decide : 339181613 ≤ 339214381) block2 block3

theorem join_1_0 : (twinPrimeSegment 339083309 339214381).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 339083309 ≤ 339148845)
    (by decide : 339148845 ≤ 339214381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 339083309 339214381).card = 448 := join_1_0

end S161C11
end Sude.GeneratedTwinScan
