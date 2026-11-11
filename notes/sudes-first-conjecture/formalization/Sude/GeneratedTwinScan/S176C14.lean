import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19260)) 370933805 370966573 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 370933805 370966573).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19260 370933805 370966573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19261)) 370966573 370999341 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 370966573 370999341).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19261 370966573 370999341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19262)) 370999341 371032109 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 370999341 371032109).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19262 370999341 371032109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19263)) 371032109 371064877 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371032109 371064877).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19263 371032109 371064877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 370933805 370999341).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 370933805 ≤ 370966573)
    (by decide : 370966573 ≤ 370999341) block0 block1

theorem join_0_1 : (twinPrimeSegment 370999341 371064877).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 370999341 ≤ 371032109)
    (by decide : 371032109 ≤ 371064877) block2 block3

theorem join_1_0 : (twinPrimeSegment 370933805 371064877).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 370933805 ≤ 370999341)
    (by decide : 370999341 ≤ 371064877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 370933805 371064877).card = 458 := join_1_0

end S176C14
end Sude.GeneratedTwinScan
