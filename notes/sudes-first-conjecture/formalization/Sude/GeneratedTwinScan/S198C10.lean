import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20410)) 416546861 416579629 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416546861 416579629).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20410 416546861 416579629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20411)) 416579629 416612397 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416579629 416612397).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20411 416579629 416612397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20411)) 416612397 416645165 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416612397 416645165).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20411 416612397 416645165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20412)) 416645165 416677933 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416645165 416677933).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20412 416645165 416677933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416546861 416612397).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 416546861 ≤ 416579629)
    (by decide : 416579629 ≤ 416612397) block0 block1

theorem join_0_1 : (twinPrimeSegment 416612397 416677933).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 416612397 ≤ 416645165)
    (by decide : 416645165 ≤ 416677933) block2 block3

theorem join_1_0 : (twinPrimeSegment 416546861 416677933).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 416546861 ≤ 416612397)
    (by decide : 416612397 ≤ 416677933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416546861 416677933).card = 470 := join_1_0

end S198C10
end Sude.GeneratedTwinScan
