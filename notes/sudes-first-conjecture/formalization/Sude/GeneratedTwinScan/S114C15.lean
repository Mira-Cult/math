import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15526)) 241041453 241074221 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241041453 241074221).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15526 241041453 241074221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15527)) 241074221 241106989 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241074221 241106989).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15527 241074221 241106989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15528)) 241106989 241139757 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241106989 241139757).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15528 241106989 241139757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15529)) 241139757 241172525 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241139757 241172525).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15529 241139757 241172525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241041453 241106989).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 241041453 ≤ 241074221)
    (by decide : 241074221 ≤ 241106989) block0 block1

theorem join_0_1 : (twinPrimeSegment 241106989 241172525).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 241106989 ≤ 241139757)
    (by decide : 241139757 ≤ 241172525) block2 block3

theorem join_1_0 : (twinPrimeSegment 241041453 241172525).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 241041453 ≤ 241106989)
    (by decide : 241106989 ≤ 241172525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241041453 241172525).card = 423 := join_1_0

end S114C15
end Sude.GeneratedTwinScan
