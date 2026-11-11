import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21882)) 478806061 478838829 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478806061 478838829).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21882 478806061 478838829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21883)) 478838829 478871597 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478838829 478871597).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21883 478838829 478871597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21883)) 478871597 478904365 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478871597 478904365).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21883 478871597 478904365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21884)) 478904365 478937133 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478904365 478937133).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21884 478904365 478937133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478806061 478871597).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 478806061 ≤ 478838829)
    (by decide : 478838829 ≤ 478871597) block0 block1

theorem join_0_1 : (twinPrimeSegment 478871597 478937133).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 478871597 ≤ 478904365)
    (by decide : 478904365 ≤ 478937133) block2 block3

theorem join_1_0 : (twinPrimeSegment 478806061 478937133).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 478806061 ≤ 478871597)
    (by decide : 478871597 ≤ 478937133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478806061 478937133).card = 450 := join_1_0

end S228C05
end Sude.GeneratedTwinScan
