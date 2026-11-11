import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17036)) 290193453 290226221 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 290193453 290226221).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17036 290193453 290226221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17036)) 290226221 290258989 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 290226221 290258989).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17036 290226221 290258989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17037)) 290258989 290291757 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 290258989 290291757).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17037 290258989 290291757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17038)) 290291757 290324525 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290291757 290324525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17038 290291757 290324525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 290193453 290258989).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 290193453 ≤ 290226221)
    (by decide : 290226221 ≤ 290258989) block0 block1

theorem join_0_1 : (twinPrimeSegment 290258989 290324525).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 290258989 ≤ 290291757)
    (by decide : 290291757 ≤ 290324525) block2 block3

theorem join_1_0 : (twinPrimeSegment 290193453 290324525).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 290193453 ≤ 290258989)
    (by decide : 290258989 ≤ 290324525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 290193453 290324525).card = 469 := join_1_0

end S138C06
end Sude.GeneratedTwinScan
