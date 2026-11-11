import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13806)) 190578733 190611501 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 190578733 190611501).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13806 190578733 190611501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13807)) 190611501 190644269 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 190611501 190644269).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13807 190611501 190644269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13808)) 190644269 190677037 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 190644269 190677037).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13808 190644269 190677037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13809)) 190677037 190709805 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 190677037 190709805).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13809 190677037 190709805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 190578733 190644269).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 190578733 ≤ 190611501)
    (by decide : 190611501 ≤ 190644269) block0 block1

theorem join_0_1 : (twinPrimeSegment 190644269 190709805).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 190644269 ≤ 190677037)
    (by decide : 190677037 ≤ 190709805) block2 block3

theorem join_1_0 : (twinPrimeSegment 190578733 190709805).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 190578733 ≤ 190644269)
    (by decide : 190644269 ≤ 190709805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 190578733 190709805).card = 461 := join_1_0

end S090C14
end Sude.GeneratedTwinScan
