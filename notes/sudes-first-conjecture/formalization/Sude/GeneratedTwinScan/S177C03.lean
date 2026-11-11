import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19277)) 371589165 371621933 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 371589165 371621933).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19277 371589165 371621933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19278)) 371621933 371654701 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 371621933 371654701).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19278 371621933 371654701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19279)) 371654701 371687469 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 371654701 371687469).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19279 371654701 371687469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19280)) 371687469 371720237 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 371687469 371720237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19280 371687469 371720237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 371589165 371654701).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 371589165 ≤ 371621933)
    (by decide : 371621933 ≤ 371654701) block0 block1

theorem join_0_1 : (twinPrimeSegment 371654701 371720237).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 371654701 ≤ 371687469)
    (by decide : 371687469 ≤ 371720237) block2 block3

theorem join_1_0 : (twinPrimeSegment 371589165 371720237).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 371589165 ≤ 371654701)
    (by decide : 371654701 ≤ 371720237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 371589165 371720237).card = 442 := join_1_0

end S177C03
end Sude.GeneratedTwinScan
