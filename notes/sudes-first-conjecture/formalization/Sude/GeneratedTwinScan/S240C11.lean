import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22467)) 504758317 504791085 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504758317 504791085).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22467 504758317 504791085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22468)) 504791085 504823853 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504791085 504823853).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22468 504791085 504823853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22469)) 504823853 504856621 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504823853 504856621).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22469 504823853 504856621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22469)) 504856621 504889389 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504856621 504889389).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22469 504856621 504889389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504758317 504823853).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 504758317 ≤ 504791085)
    (by decide : 504791085 ≤ 504823853) block0 block1

theorem join_0_1 : (twinPrimeSegment 504823853 504889389).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 504823853 ≤ 504856621)
    (by decide : 504856621 ≤ 504889389) block2 block3

theorem join_1_0 : (twinPrimeSegment 504758317 504889389).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 504758317 ≤ 504823853)
    (by decide : 504823853 ≤ 504889389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504758317 504889389).card = 429 := join_1_0

end S240C11
end Sude.GeneratedTwinScan
