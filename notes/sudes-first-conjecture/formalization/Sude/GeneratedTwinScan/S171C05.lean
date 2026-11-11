import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18955)) 359268397 359301165 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359268397 359301165).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18955 359268397 359301165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18956)) 359301165 359333933 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359301165 359333933).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18956 359301165 359333933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18956)) 359333933 359366701 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359333933 359366701).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18956 359333933 359366701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18957)) 359366701 359399469 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359366701 359399469).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18957 359366701 359399469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359268397 359333933).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 359268397 ≤ 359301165)
    (by decide : 359301165 ≤ 359333933) block0 block1

theorem join_0_1 : (twinPrimeSegment 359333933 359399469).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 359333933 ≤ 359366701)
    (by decide : 359366701 ≤ 359399469) block2 block3

theorem join_1_0 : (twinPrimeSegment 359268397 359399469).card = 405 := by
  simpa using combineTwinPrimeSegments (by decide : 359268397 ≤ 359333933)
    (by decide : 359333933 ≤ 359399469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359268397 359399469).card = 405 := join_1_0

end S171C05
end Sude.GeneratedTwinScan
