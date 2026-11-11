import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21986)) 483393581 483426349 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483393581 483426349).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21986 483393581 483426349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21987)) 483426349 483459117 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483426349 483459117).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21987 483426349 483459117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21988)) 483459117 483491885 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483459117 483491885).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21988 483459117 483491885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21989)) 483491885 483524653 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483491885 483524653).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21989 483491885 483524653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483393581 483459117).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 483393581 ≤ 483426349)
    (by decide : 483426349 ≤ 483459117) block0 block1

theorem join_0_1 : (twinPrimeSegment 483459117 483524653).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 483459117 ≤ 483491885)
    (by decide : 483491885 ≤ 483524653) block2 block3

theorem join_1_0 : (twinPrimeSegment 483393581 483524653).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 483393581 ≤ 483459117)
    (by decide : 483459117 ≤ 483524653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483393581 483524653).card = 457 := join_1_0

end S230C08
end Sude.GeneratedTwinScan
