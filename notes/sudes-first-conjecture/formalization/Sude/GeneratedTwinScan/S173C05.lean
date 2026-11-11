import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19065)) 363462701 363495469 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363462701 363495469).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19065 363462701 363495469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19066)) 363495469 363528237 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363495469 363528237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19066 363495469 363528237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19067)) 363528237 363561005 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363528237 363561005).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19067 363528237 363561005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19068)) 363561005 363593773 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363561005 363593773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19068 363561005 363593773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363462701 363528237).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 363462701 ≤ 363495469)
    (by decide : 363495469 ≤ 363528237) block0 block1

theorem join_0_1 : (twinPrimeSegment 363528237 363593773).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 363528237 ≤ 363561005)
    (by decide : 363561005 ≤ 363593773) block2 block3

theorem join_1_0 : (twinPrimeSegment 363462701 363593773).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 363462701 ≤ 363528237)
    (by decide : 363528237 ≤ 363593773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363462701 363593773).card = 453 := join_1_0

end S173C05
end Sude.GeneratedTwinScan
