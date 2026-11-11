import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13610)) 185204781 185237549 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185204781 185237549).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13610 185204781 185237549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13611)) 185237549 185270317 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185237549 185270317).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13611 185237549 185270317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13612)) 185270317 185303085 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185270317 185303085).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13612 185270317 185303085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13613)) 185303085 185335853 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185303085 185335853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13613 185303085 185335853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185204781 185270317).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 185204781 ≤ 185237549)
    (by decide : 185237549 ≤ 185270317) block0 block1

theorem join_0_1 : (twinPrimeSegment 185270317 185335853).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 185270317 ≤ 185303085)
    (by decide : 185303085 ≤ 185335853) block2 block3

theorem join_1_0 : (twinPrimeSegment 185204781 185335853).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 185204781 ≤ 185270317)
    (by decide : 185270317 ≤ 185335853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185204781 185335853).card = 464 := join_1_0

end S088C05
end Sude.GeneratedTwinScan
