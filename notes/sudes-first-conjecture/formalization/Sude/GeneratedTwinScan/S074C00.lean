import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12458)) 155189293 155222061 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155189293 155222061).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12458 155189293 155222061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12460)) 155222061 155254829 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155222061 155254829).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12460 155222061 155254829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12461)) 155254829 155287597 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155254829 155287597).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12461 155254829 155287597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12462)) 155287597 155320365 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155287597 155320365).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12462 155287597 155320365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155189293 155254829).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 155222061)
    (by decide : 155222061 ≤ 155254829) block0 block1

theorem join_0_1 : (twinPrimeSegment 155254829 155320365).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 155254829 ≤ 155287597)
    (by decide : 155287597 ≤ 155320365) block2 block3

theorem join_1_0 : (twinPrimeSegment 155189293 155320365).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 155254829)
    (by decide : 155254829 ≤ 155320365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155189293 155320365).card = 495 := join_1_0

end S074C00
end Sude.GeneratedTwinScan
