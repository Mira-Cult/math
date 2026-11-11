import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16155)) 260964397 260997165 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260964397 260997165).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16155 260964397 260997165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16156)) 260997165 261029933 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260997165 261029933).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16156 260997165 261029933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16157)) 261029933 261062701 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 261029933 261062701).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16157 261029933 261062701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16158)) 261062701 261095469 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 261062701 261095469).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16158 261062701 261095469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260964397 261029933).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 260964397 ≤ 260997165)
    (by decide : 260997165 ≤ 261029933) block0 block1

theorem join_0_1 : (twinPrimeSegment 261029933 261095469).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 261029933 ≤ 261062701)
    (by decide : 261062701 ≤ 261095469) block2 block3

theorem join_1_0 : (twinPrimeSegment 260964397 261095469).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 260964397 ≤ 261029933)
    (by decide : 261029933 ≤ 261095469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260964397 261095469).card = 487 := join_1_0

end S124C07
end Sude.GeneratedTwinScan
