import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19510)) 380633133 380665901 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380633133 380665901).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19510 380633133 380665901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19511)) 380665901 380698669 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380665901 380698669).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19511 380665901 380698669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19512)) 380698669 380731437 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380698669 380731437).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19512 380698669 380731437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19513)) 380731437 380764205 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380731437 380764205).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19513 380731437 380764205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380633133 380698669).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 380633133 ≤ 380665901)
    (by decide : 380665901 ≤ 380698669) block0 block1

theorem join_0_1 : (twinPrimeSegment 380698669 380764205).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 380698669 ≤ 380731437)
    (by decide : 380731437 ≤ 380764205) block2 block3

theorem join_1_0 : (twinPrimeSegment 380633133 380764205).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 380633133 ≤ 380698669)
    (by decide : 380698669 ≤ 380764205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380633133 380764205).card = 462 := join_1_0

end S181C08
end Sude.GeneratedTwinScan
