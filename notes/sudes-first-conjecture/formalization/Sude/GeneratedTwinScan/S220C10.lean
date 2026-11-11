import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21510)) 462684205 462716973 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462684205 462716973).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21510 462684205 462716973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21511)) 462716973 462749741 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462716973 462749741).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21511 462716973 462749741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21512)) 462749741 462782509 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462749741 462782509).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21512 462749741 462782509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21513)) 462782509 462815277 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462782509 462815277).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21513 462782509 462815277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462684205 462749741).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 462684205 ≤ 462716973)
    (by decide : 462716973 ≤ 462749741) block0 block1

theorem join_0_1 : (twinPrimeSegment 462749741 462815277).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 462749741 ≤ 462782509)
    (by decide : 462782509 ≤ 462815277) block2 block3

theorem join_1_0 : (twinPrimeSegment 462684205 462815277).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 462684205 ≤ 462749741)
    (by decide : 462749741 ≤ 462815277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462684205 462815277).card = 437 := join_1_0

end S220C10
end Sude.GeneratedTwinScan
