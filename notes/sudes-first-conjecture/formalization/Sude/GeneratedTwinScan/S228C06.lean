import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21885)) 478937133 478969901 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478937133 478969901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21885 478937133 478969901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21886)) 478969901 479002669 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478969901 479002669).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21886 478969901 479002669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21886)) 479002669 479035437 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 479002669 479035437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21886 479002669 479035437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21887)) 479035437 479068205 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 479035437 479068205).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21887 479035437 479068205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478937133 479002669).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 478937133 ≤ 478969901)
    (by decide : 478969901 ≤ 479002669) block0 block1

theorem join_0_1 : (twinPrimeSegment 479002669 479068205).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 479002669 ≤ 479035437)
    (by decide : 479035437 ≤ 479068205) block2 block3

theorem join_1_0 : (twinPrimeSegment 478937133 479068205).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 478937133 ≤ 479002669)
    (by decide : 479002669 ≤ 479068205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478937133 479068205).card = 432 := join_1_0

end S228C06
end Sude.GeneratedTwinScan
