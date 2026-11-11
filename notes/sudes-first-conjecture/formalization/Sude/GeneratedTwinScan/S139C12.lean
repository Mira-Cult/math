import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17120)) 293077037 293109805 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 293077037 293109805).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17120 293077037 293109805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17121)) 293109805 293142573 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 293109805 293142573).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17121 293109805 293142573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17122)) 293142573 293175341 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293142573 293175341).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17122 293142573 293175341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17123)) 293175341 293208109 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293175341 293208109).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17123 293175341 293208109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 293077037 293142573).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 293077037 ≤ 293109805)
    (by decide : 293109805 ≤ 293142573) block0 block1

theorem join_0_1 : (twinPrimeSegment 293142573 293208109).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 293142573 ≤ 293175341)
    (by decide : 293175341 ≤ 293208109) block2 block3

theorem join_1_0 : (twinPrimeSegment 293077037 293208109).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 293077037 ≤ 293142573)
    (by decide : 293142573 ≤ 293208109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 293077037 293208109).card = 440 := join_1_0

end S139C12
end Sude.GeneratedTwinScan
