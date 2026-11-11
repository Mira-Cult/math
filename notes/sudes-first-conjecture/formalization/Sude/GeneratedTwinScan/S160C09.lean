import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18350)) 336724013 336756781 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336724013 336756781).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18350 336724013 336756781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18351)) 336756781 336789549 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336756781 336789549).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18351 336756781 336789549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18352)) 336789549 336822317 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336789549 336822317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18352 336789549 336822317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18353)) 336822317 336855085 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336822317 336855085).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18353 336822317 336855085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336724013 336789549).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 336724013 ≤ 336756781)
    (by decide : 336756781 ≤ 336789549) block0 block1

theorem join_0_1 : (twinPrimeSegment 336789549 336855085).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 336789549 ≤ 336822317)
    (by decide : 336822317 ≤ 336855085) block2 block3

theorem join_1_0 : (twinPrimeSegment 336724013 336855085).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 336724013 ≤ 336789549)
    (by decide : 336789549 ≤ 336855085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336724013 336855085).card = 454 := join_1_0

end S160C09
end Sude.GeneratedTwinScan
