import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16717)) 279445549 279478317 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279445549 279478317).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16717 279445549 279478317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16718)) 279478317 279511085 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279478317 279511085).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16718 279478317 279511085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16719)) 279511085 279543853 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279511085 279543853).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16719 279511085 279543853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16720)) 279543853 279576621 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279543853 279576621).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16720 279543853 279576621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279445549 279511085).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 279445549 ≤ 279478317)
    (by decide : 279478317 ≤ 279511085) block0 block1

theorem join_0_1 : (twinPrimeSegment 279511085 279576621).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 279511085 ≤ 279543853)
    (by decide : 279543853 ≤ 279576621) block2 block3

theorem join_1_0 : (twinPrimeSegment 279445549 279576621).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 279445549 ≤ 279511085)
    (by decide : 279511085 ≤ 279576621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279445549 279576621).card = 449 := join_1_0

end S133C04
end Sude.GeneratedTwinScan
