import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16480)) 271581229 271613997 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271581229 271613997).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16480 271581229 271613997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16481)) 271613997 271646765 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271613997 271646765).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16481 271613997 271646765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16482)) 271646765 271679533 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271646765 271679533).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16482 271646765 271679533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16483)) 271679533 271712301 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271679533 271712301).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16483 271679533 271712301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271581229 271646765).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 271581229 ≤ 271613997)
    (by decide : 271613997 ≤ 271646765) block0 block1

theorem join_0_1 : (twinPrimeSegment 271646765 271712301).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 271646765 ≤ 271679533)
    (by decide : 271679533 ≤ 271712301) block2 block3

theorem join_1_0 : (twinPrimeSegment 271581229 271712301).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 271581229 ≤ 271646765)
    (by decide : 271646765 ≤ 271712301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271581229 271712301).card = 458 := join_1_0

end S129C08
end Sude.GeneratedTwinScan
