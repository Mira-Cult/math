import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18694)) 349437997 349470765 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349437997 349470765).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18694 349437997 349470765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18695)) 349470765 349503533 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349470765 349503533).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18695 349470765 349503533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18695)) 349503533 349536301 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349503533 349536301).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18695 349503533 349536301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18696)) 349536301 349569069 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349536301 349569069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18696 349536301 349569069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349437997 349503533).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 349437997 ≤ 349470765)
    (by decide : 349470765 ≤ 349503533) block0 block1

theorem join_0_1 : (twinPrimeSegment 349503533 349569069).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 349503533 ≤ 349536301)
    (by decide : 349536301 ≤ 349569069) block2 block3

theorem join_1_0 : (twinPrimeSegment 349437997 349569069).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 349437997 ≤ 349503533)
    (by decide : 349503533 ≤ 349569069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349437997 349569069).card = 458 := join_1_0

end S166C10
end Sude.GeneratedTwinScan
