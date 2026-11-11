import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19409)) 376700973 376733741 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376700973 376733741).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19409 376700973 376733741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19410)) 376733741 376766509 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376733741 376766509).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19410 376733741 376766509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19411)) 376766509 376799277 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376766509 376799277).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19411 376766509 376799277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19412)) 376799277 376832045 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376799277 376832045).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19412 376799277 376832045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376700973 376766509).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 376700973 ≤ 376733741)
    (by decide : 376733741 ≤ 376766509) block0 block1

theorem join_0_1 : (twinPrimeSegment 376766509 376832045).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 376766509 ≤ 376799277)
    (by decide : 376799277 ≤ 376832045) block2 block3

theorem join_1_0 : (twinPrimeSegment 376700973 376832045).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 376700973 ≤ 376766509)
    (by decide : 376766509 ≤ 376832045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376700973 376832045).card = 436 := join_1_0

end S179C10
end Sude.GeneratedTwinScan
