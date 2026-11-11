import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S199C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20461)) 418644013 418676781 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 418644013 418676781).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20461 418644013 418676781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20462)) 418676781 418709549 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 418676781 418709549).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20462 418676781 418709549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20463)) 418709549 418742317 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 418709549 418742317).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20463 418709549 418742317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20463)) 418742317 418775085 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 418742317 418775085).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20463 418742317 418775085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 418644013 418709549).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 418644013 ≤ 418676781)
    (by decide : 418676781 ≤ 418709549) block0 block1

theorem join_0_1 : (twinPrimeSegment 418709549 418775085).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 418709549 ≤ 418742317)
    (by decide : 418742317 ≤ 418775085) block2 block3

theorem join_1_0 : (twinPrimeSegment 418644013 418775085).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 418644013 ≤ 418709549)
    (by decide : 418709549 ≤ 418775085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 418644013 418775085).card = 447 := join_1_0

end S199C10
end Sude.GeneratedTwinScan
