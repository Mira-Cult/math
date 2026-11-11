import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12755)) 162660397 162693165 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162660397 162693165).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12755 162660397 162693165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12756)) 162693165 162725933 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162693165 162725933).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12756 162693165 162725933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12757)) 162725933 162758701 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162725933 162758701).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12757 162725933 162758701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12758)) 162758701 162791469 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162758701 162791469).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12758 162758701 162791469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162660397 162725933).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 162660397 ≤ 162693165)
    (by decide : 162693165 ≤ 162725933) block0 block1

theorem join_0_1 : (twinPrimeSegment 162725933 162791469).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 162725933 ≤ 162758701)
    (by decide : 162758701 ≤ 162791469) block2 block3

theorem join_1_0 : (twinPrimeSegment 162660397 162791469).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 162660397 ≤ 162725933)
    (by decide : 162725933 ≤ 162791469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162660397 162791469).card = 504 := join_1_0

end S077C09
end Sude.GeneratedTwinScan
