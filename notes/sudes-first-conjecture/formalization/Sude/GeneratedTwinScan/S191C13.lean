import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20057)) 402260013 402292781 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402260013 402292781).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20057 402260013 402292781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20058)) 402292781 402325549 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402292781 402325549).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20058 402292781 402325549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20058)) 402325549 402358317 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402325549 402358317).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20058 402325549 402358317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20059)) 402358317 402391085 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 402358317 402391085).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20059 402358317 402391085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402260013 402325549).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 402260013 ≤ 402292781)
    (by decide : 402292781 ≤ 402325549) block0 block1

theorem join_0_1 : (twinPrimeSegment 402325549 402391085).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 402325549 ≤ 402358317)
    (by decide : 402358317 ≤ 402391085) block2 block3

theorem join_1_0 : (twinPrimeSegment 402260013 402391085).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 402260013 ≤ 402325549)
    (by decide : 402325549 ≤ 402391085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402260013 402391085).card = 435 := join_1_0

end S191C13
end Sude.GeneratedTwinScan
