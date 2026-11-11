import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18407)) 338821165 338853933 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338821165 338853933).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18407 338821165 338853933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18408)) 338853933 338886701 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338853933 338886701).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18408 338853933 338886701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18409)) 338886701 338919469 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338886701 338919469).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18409 338886701 338919469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18410)) 338919469 338952237 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338919469 338952237).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18410 338919469 338952237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338821165 338886701).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 338821165 ≤ 338853933)
    (by decide : 338853933 ≤ 338886701) block0 block1

theorem join_0_1 : (twinPrimeSegment 338886701 338952237).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 338886701 ≤ 338919469)
    (by decide : 338919469 ≤ 338952237) block2 block3

theorem join_1_0 : (twinPrimeSegment 338821165 338952237).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 338821165 ≤ 338886701)
    (by decide : 338886701 ≤ 338952237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338821165 338952237).card = 435 := join_1_0

end S161C09
end Sude.GeneratedTwinScan
