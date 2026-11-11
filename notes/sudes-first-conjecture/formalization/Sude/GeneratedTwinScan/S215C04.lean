import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S215C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21247)) 451412013 451444781 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 451412013 451444781).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21247 451412013 451444781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21248)) 451444781 451477549 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 451444781 451477549).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21248 451444781 451477549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21248)) 451477549 451510317 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 451477549 451510317).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21248 451477549 451510317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21249)) 451510317 451543085 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 451510317 451543085).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21249 451510317 451543085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 451412013 451477549).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 451412013 ≤ 451444781)
    (by decide : 451444781 ≤ 451477549) block0 block1

theorem join_0_1 : (twinPrimeSegment 451477549 451543085).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 451477549 ≤ 451510317)
    (by decide : 451510317 ≤ 451543085) block2 block3

theorem join_1_0 : (twinPrimeSegment 451412013 451543085).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 451412013 ≤ 451477549)
    (by decide : 451477549 ≤ 451543085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 451412013 451543085).card = 450 := join_1_0

end S215C04
end Sude.GeneratedTwinScan
