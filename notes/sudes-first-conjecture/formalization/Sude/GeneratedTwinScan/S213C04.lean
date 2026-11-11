import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21148)) 447217709 447250477 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447217709 447250477).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21148 447217709 447250477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21149)) 447250477 447283245 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447250477 447283245).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21149 447250477 447283245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21149)) 447283245 447316013 = 80 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447283245 447316013).card = 80 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21149 447283245 447316013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21150)) 447316013 447348781 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447316013 447348781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21150 447316013 447348781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447217709 447283245).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 447217709 ≤ 447250477)
    (by decide : 447250477 ≤ 447283245) block0 block1

theorem join_0_1 : (twinPrimeSegment 447283245 447348781).card = 190 := by
  simpa using combineTwinPrimeSegments (by decide : 447283245 ≤ 447316013)
    (by decide : 447316013 ≤ 447348781) block2 block3

theorem join_1_0 : (twinPrimeSegment 447217709 447348781).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 447217709 ≤ 447283245)
    (by decide : 447283245 ≤ 447348781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447217709 447348781).card = 409 := join_1_0

end S213C04
end Sude.GeneratedTwinScan
