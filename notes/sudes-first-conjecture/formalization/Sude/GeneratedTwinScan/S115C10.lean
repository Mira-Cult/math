import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15572)) 242483245 242516013 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242483245 242516013).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15572 242483245 242516013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15573)) 242516013 242548781 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242516013 242548781).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15573 242516013 242548781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15575)) 242548781 242581549 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242548781 242581549).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15575 242548781 242581549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15576)) 242581549 242614317 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242581549 242614317).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15576 242581549 242614317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242483245 242548781).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 242483245 ≤ 242516013)
    (by decide : 242516013 ≤ 242548781) block0 block1

theorem join_0_1 : (twinPrimeSegment 242548781 242614317).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 242548781 ≤ 242581549)
    (by decide : 242581549 ≤ 242614317) block2 block3

theorem join_1_0 : (twinPrimeSegment 242483245 242614317).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 242483245 ≤ 242548781)
    (by decide : 242548781 ≤ 242614317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242483245 242614317).card = 445 := join_1_0

end S115C10
end Sude.GeneratedTwinScan
