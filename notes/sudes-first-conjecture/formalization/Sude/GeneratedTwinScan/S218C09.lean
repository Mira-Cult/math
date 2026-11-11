import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21410)) 458358829 458391597 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458358829 458391597).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21410 458358829 458391597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21410)) 458391597 458424365 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458391597 458424365).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21410 458391597 458424365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21411)) 458424365 458457133 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458424365 458457133).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21411 458424365 458457133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21412)) 458457133 458489901 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458457133 458489901).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21412 458457133 458489901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458358829 458424365).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 458358829 ≤ 458391597)
    (by decide : 458391597 ≤ 458424365) block0 block1

theorem join_0_1 : (twinPrimeSegment 458424365 458489901).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 458424365 ≤ 458457133)
    (by decide : 458457133 ≤ 458489901) block2 block3

theorem join_1_0 : (twinPrimeSegment 458358829 458489901).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 458358829 ≤ 458424365)
    (by decide : 458424365 ≤ 458489901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458358829 458489901).card = 433 := join_1_0

end S218C09
end Sude.GeneratedTwinScan
