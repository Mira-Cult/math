import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19800)) 392036397 392069165 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392036397 392069165).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19800 392036397 392069165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19801)) 392069165 392101933 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392069165 392101933).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19801 392069165 392101933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19802)) 392101933 392134701 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392101933 392134701).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19802 392101933 392134701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19803)) 392134701 392167469 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392134701 392167469).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19803 392134701 392167469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392036397 392101933).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 392036397 ≤ 392069165)
    (by decide : 392069165 ≤ 392101933) block0 block1

theorem join_0_1 : (twinPrimeSegment 392101933 392167469).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 392101933 ≤ 392134701)
    (by decide : 392134701 ≤ 392167469) block2 block3

theorem join_1_0 : (twinPrimeSegment 392036397 392167469).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 392036397 ≤ 392101933)
    (by decide : 392101933 ≤ 392167469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392036397 392167469).card = 454 := join_1_0

end S186C15
end Sude.GeneratedTwinScan
