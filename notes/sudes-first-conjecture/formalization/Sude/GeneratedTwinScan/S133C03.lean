import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16713)) 279314477 279347245 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279314477 279347245).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16713 279314477 279347245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16714)) 279347245 279380013 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279347245 279380013).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16714 279347245 279380013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16715)) 279380013 279412781 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279380013 279412781).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16715 279380013 279412781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16716)) 279412781 279445549 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279412781 279445549).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16716 279412781 279445549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279314477 279380013).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 279314477 ≤ 279347245)
    (by decide : 279347245 ≤ 279380013) block0 block1

theorem join_0_1 : (twinPrimeSegment 279380013 279445549).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 279380013 ≤ 279412781)
    (by decide : 279412781 ≤ 279445549) block2 block3

theorem join_1_0 : (twinPrimeSegment 279314477 279445549).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 279314477 ≤ 279380013)
    (by decide : 279380013 ≤ 279445549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279314477 279445549).card = 491 := join_1_0

end S133C03
end Sude.GeneratedTwinScan
