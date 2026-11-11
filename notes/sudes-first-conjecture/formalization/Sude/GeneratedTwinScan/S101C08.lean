import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14590)) 212860973 212893741 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 212860973 212893741).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14590 212860973 212893741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14592)) 212893741 212926509 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 212893741 212926509).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14592 212893741 212926509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14593)) 212926509 212959277 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 212926509 212959277).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14593 212926509 212959277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14594)) 212959277 212992045 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 212959277 212992045).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14594 212959277 212992045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 212860973 212926509).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 212860973 ≤ 212893741)
    (by decide : 212893741 ≤ 212926509) block0 block1

theorem join_0_1 : (twinPrimeSegment 212926509 212992045).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 212926509 ≤ 212959277)
    (by decide : 212959277 ≤ 212992045) block2 block3

theorem join_1_0 : (twinPrimeSegment 212860973 212992045).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 212860973 ≤ 212926509)
    (by decide : 212926509 ≤ 212992045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 212860973 212992045).card = 488 := join_1_0

end S101C08
end Sude.GeneratedTwinScan
