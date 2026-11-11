import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18250)) 333053997 333086765 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333053997 333086765).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18250 333053997 333086765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18251)) 333086765 333119533 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333086765 333119533).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18251 333086765 333119533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18252)) 333119533 333152301 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333119533 333152301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18252 333119533 333152301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18253)) 333152301 333185069 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333152301 333185069).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18253 333152301 333185069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333053997 333119533).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 333053997 ≤ 333086765)
    (by decide : 333086765 ≤ 333119533) block0 block1

theorem join_0_1 : (twinPrimeSegment 333119533 333185069).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 333119533 ≤ 333152301)
    (by decide : 333152301 ≤ 333185069) block2 block3

theorem join_1_0 : (twinPrimeSegment 333053997 333185069).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 333053997 ≤ 333119533)
    (by decide : 333119533 ≤ 333185069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333053997 333185069).card = 450 := join_1_0

end S158C13
end Sude.GeneratedTwinScan
