import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12479)) 155713581 155746349 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155713581 155746349).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12479 155713581 155746349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12481)) 155746349 155779117 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155746349 155779117).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12481 155746349 155779117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12482)) 155779117 155811885 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155779117 155811885).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12482 155779117 155811885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12483)) 155811885 155844653 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155811885 155844653).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12483 155811885 155844653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155713581 155779117).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 155713581 ≤ 155746349)
    (by decide : 155746349 ≤ 155779117) block0 block1

theorem join_0_1 : (twinPrimeSegment 155779117 155844653).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 155779117 ≤ 155811885)
    (by decide : 155811885 ≤ 155844653) block2 block3

theorem join_1_0 : (twinPrimeSegment 155713581 155844653).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 155713581 ≤ 155779117)
    (by decide : 155779117 ≤ 155844653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155713581 155844653).card = 492 := join_1_0

end S074C04
end Sude.GeneratedTwinScan
