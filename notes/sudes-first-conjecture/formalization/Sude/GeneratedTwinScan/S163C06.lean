import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18510)) 342622253 342655021 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 342622253 342655021).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18510 342622253 342655021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18511)) 342655021 342687789 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 342655021 342687789).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18511 342655021 342687789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18512)) 342687789 342720557 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 342687789 342720557).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18512 342687789 342720557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18513)) 342720557 342753325 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 342720557 342753325).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18513 342720557 342753325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 342622253 342687789).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 342622253 ≤ 342655021)
    (by decide : 342655021 ≤ 342687789) block0 block1

theorem join_0_1 : (twinPrimeSegment 342687789 342753325).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 342687789 ≤ 342720557)
    (by decide : 342720557 ≤ 342753325) block2 block3

theorem join_1_0 : (twinPrimeSegment 342622253 342753325).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 342622253 ≤ 342687789)
    (by decide : 342687789 ≤ 342753325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 342622253 342753325).card = 451 := join_1_0

end S163C06
end Sude.GeneratedTwinScan
