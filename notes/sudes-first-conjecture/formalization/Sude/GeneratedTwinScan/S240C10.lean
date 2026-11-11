import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22464)) 504627245 504660013 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504627245 504660013).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22464 504627245 504660013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22465)) 504660013 504692781 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504660013 504692781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22465 504660013 504692781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22466)) 504692781 504725549 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504692781 504725549).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22466 504692781 504725549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22466)) 504725549 504758317 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504725549 504758317).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22466 504725549 504758317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504627245 504692781).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 504627245 ≤ 504660013)
    (by decide : 504660013 ≤ 504692781) block0 block1

theorem join_0_1 : (twinPrimeSegment 504692781 504758317).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 504692781 ≤ 504725549)
    (by decide : 504725549 ≤ 504758317) block2 block3

theorem join_1_0 : (twinPrimeSegment 504627245 504758317).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 504627245 ≤ 504692781)
    (by decide : 504692781 ≤ 504758317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504627245 504758317).card = 442 := join_1_0

end S240C10
end Sude.GeneratedTwinScan
