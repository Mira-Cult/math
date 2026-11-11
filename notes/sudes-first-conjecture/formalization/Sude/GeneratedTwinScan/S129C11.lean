import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16492)) 271974445 272007213 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271974445 272007213).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16492 271974445 272007213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16493)) 272007213 272039981 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272007213 272039981).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16493 272007213 272039981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16494)) 272039981 272072749 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272039981 272072749).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16494 272039981 272072749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16495)) 272072749 272105517 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272072749 272105517).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16495 272072749 272105517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271974445 272039981).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 271974445 ≤ 272007213)
    (by decide : 272007213 ≤ 272039981) block0 block1

theorem join_0_1 : (twinPrimeSegment 272039981 272105517).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 272039981 ≤ 272072749)
    (by decide : 272072749 ≤ 272105517) block2 block3

theorem join_1_0 : (twinPrimeSegment 271974445 272105517).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 271974445 ≤ 272039981)
    (by decide : 272039981 ≤ 272105517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271974445 272105517).card = 469 := join_1_0

end S129C11
end Sude.GeneratedTwinScan
