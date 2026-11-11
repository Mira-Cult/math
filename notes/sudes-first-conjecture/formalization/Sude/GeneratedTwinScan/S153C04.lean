import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17928)) 321388589 321421357 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321388589 321421357).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17928 321388589 321421357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17929)) 321421357 321454125 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321421357 321454125).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17929 321421357 321454125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17930)) 321454125 321486893 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321454125 321486893).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17930 321454125 321486893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17930)) 321486893 321519661 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321486893 321519661).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17930 321486893 321519661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321388589 321454125).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 321388589 ≤ 321421357)
    (by decide : 321421357 ≤ 321454125) block0 block1

theorem join_0_1 : (twinPrimeSegment 321454125 321519661).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 321454125 ≤ 321486893)
    (by decide : 321486893 ≤ 321519661) block2 block3

theorem join_1_0 : (twinPrimeSegment 321388589 321519661).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 321388589 ≤ 321454125)
    (by decide : 321454125 ≤ 321519661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321388589 321519661).card = 428 := join_1_0

end S153C04
end Sude.GeneratedTwinScan
