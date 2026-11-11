import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21397)) 457834541 457867309 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 457834541 457867309).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21397 457834541 457867309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21398)) 457867309 457900077 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 457867309 457900077).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21398 457867309 457900077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21399)) 457900077 457932845 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 457900077 457932845).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21399 457900077 457932845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21400)) 457932845 457965613 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 457932845 457965613).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21400 457932845 457965613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 457834541 457900077).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 457834541 ≤ 457867309)
    (by decide : 457867309 ≤ 457900077) block0 block1

theorem join_0_1 : (twinPrimeSegment 457900077 457965613).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 457900077 ≤ 457932845)
    (by decide : 457932845 ≤ 457965613) block2 block3

theorem join_1_0 : (twinPrimeSegment 457834541 457965613).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 457834541 ≤ 457900077)
    (by decide : 457900077 ≤ 457965613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 457834541 457965613).card = 422 := join_1_0

end S218C05
end Sude.GeneratedTwinScan
