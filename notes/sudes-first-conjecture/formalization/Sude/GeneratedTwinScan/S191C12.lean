import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20053)) 402128941 402161709 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402128941 402161709).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20053 402128941 402161709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20054)) 402161709 402194477 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402161709 402194477).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20054 402161709 402194477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20055)) 402194477 402227245 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402194477 402227245).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20055 402194477 402227245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20056)) 402227245 402260013 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402227245 402260013).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20056 402227245 402260013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402128941 402194477).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 402128941 ≤ 402161709)
    (by decide : 402161709 ≤ 402194477) block0 block1

theorem join_0_1 : (twinPrimeSegment 402194477 402260013).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 402194477 ≤ 402227245)
    (by decide : 402227245 ≤ 402260013) block2 block3

theorem join_1_0 : (twinPrimeSegment 402128941 402260013).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 402128941 ≤ 402194477)
    (by decide : 402194477 ≤ 402260013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402128941 402260013).card = 441 := join_1_0

end S191C12
end Sude.GeneratedTwinScan
