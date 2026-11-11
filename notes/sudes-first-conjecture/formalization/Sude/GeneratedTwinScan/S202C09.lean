import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20611)) 424804397 424837165 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424804397 424837165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20611 424804397 424837165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20612)) 424837165 424869933 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424837165 424869933).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20612 424837165 424869933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20613)) 424869933 424902701 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424869933 424902701).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20613 424869933 424902701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20613)) 424902701 424935469 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424902701 424935469).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20613 424902701 424935469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424804397 424869933).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 424804397 ≤ 424837165)
    (by decide : 424837165 ≤ 424869933) block0 block1

theorem join_0_1 : (twinPrimeSegment 424869933 424935469).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 424869933 ≤ 424902701)
    (by decide : 424902701 ≤ 424935469) block2 block3

theorem join_1_0 : (twinPrimeSegment 424804397 424935469).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 424804397 ≤ 424869933)
    (by decide : 424869933 ≤ 424935469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424804397 424935469).card = 442 := join_1_0

end S202C09
end Sude.GeneratedTwinScan
