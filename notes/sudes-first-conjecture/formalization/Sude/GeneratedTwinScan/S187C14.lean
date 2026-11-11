import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19850)) 394002477 394035245 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394002477 394035245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19850 394002477 394035245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19851)) 394035245 394068013 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394035245 394068013).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19851 394035245 394068013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19851)) 394068013 394100781 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394068013 394100781).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19851 394068013 394100781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19852)) 394100781 394133549 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394100781 394133549).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19852 394100781 394133549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394002477 394068013).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 394002477 ≤ 394035245)
    (by decide : 394035245 ≤ 394068013) block0 block1

theorem join_0_1 : (twinPrimeSegment 394068013 394133549).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 394068013 ≤ 394100781)
    (by decide : 394100781 ≤ 394133549) block2 block3

theorem join_1_0 : (twinPrimeSegment 394002477 394133549).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 394002477 ≤ 394068013)
    (by decide : 394068013 ≤ 394133549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394002477 394133549).card = 441 := join_1_0

end S187C14
end Sude.GeneratedTwinScan
