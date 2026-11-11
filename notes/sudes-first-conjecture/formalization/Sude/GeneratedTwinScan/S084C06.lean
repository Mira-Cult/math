import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13303)) 176947245 176980013 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176947245 176980013).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13303 176947245 176980013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13304)) 176980013 177012781 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176980013 177012781).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13304 176980013 177012781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13305)) 177012781 177045549 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177012781 177045549).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13305 177012781 177045549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13307)) 177045549 177078317 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177045549 177078317).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13307 177045549 177078317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176947245 177012781).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 176947245 ≤ 176980013)
    (by decide : 176980013 ≤ 177012781) block0 block1

theorem join_0_1 : (twinPrimeSegment 177012781 177078317).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 177012781 ≤ 177045549)
    (by decide : 177045549 ≤ 177078317) block2 block3

theorem join_1_0 : (twinPrimeSegment 176947245 177078317).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 176947245 ≤ 177012781)
    (by decide : 177012781 ≤ 177078317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176947245 177078317).card = 481 := join_1_0

end S084C06
end Sude.GeneratedTwinScan
