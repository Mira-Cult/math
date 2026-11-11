import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20563)) 422838317 422871085 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422838317 422871085).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20563 422838317 422871085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20564)) 422871085 422903853 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422871085 422903853).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20564 422871085 422903853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20565)) 422903853 422936621 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422903853 422936621).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20565 422903853 422936621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20566)) 422936621 422969389 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422936621 422969389).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20566 422936621 422969389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422838317 422903853).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 422838317 ≤ 422871085)
    (by decide : 422871085 ≤ 422903853) block0 block1

theorem join_0_1 : (twinPrimeSegment 422903853 422969389).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 422903853 ≤ 422936621)
    (by decide : 422936621 ≤ 422969389) block2 block3

theorem join_1_0 : (twinPrimeSegment 422838317 422969389).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 422838317 ≤ 422903853)
    (by decide : 422903853 ≤ 422969389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422838317 422969389).card = 434 := join_1_0

end S201C10
end Sude.GeneratedTwinScan
