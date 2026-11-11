import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22517)) 506986541 507019309 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506986541 507019309).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22517 506986541 507019309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22517)) 507019309 507052077 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507019309 507052077).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22517 507019309 507052077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22518)) 507052077 507084845 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507052077 507084845).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22518 507052077 507084845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22519)) 507084845 507117613 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507084845 507117613).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22519 507084845 507117613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506986541 507052077).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 506986541 ≤ 507019309)
    (by decide : 507019309 ≤ 507052077) block0 block1

theorem join_0_1 : (twinPrimeSegment 507052077 507117613).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 507052077 ≤ 507084845)
    (by decide : 507084845 ≤ 507117613) block2 block3

theorem join_1_0 : (twinPrimeSegment 506986541 507117613).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 506986541 ≤ 507052077)
    (by decide : 507052077 ≤ 507117613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506986541 507117613).card = 428 := join_1_0

end S241C12
end Sude.GeneratedTwinScan
