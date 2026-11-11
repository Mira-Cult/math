import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19731)) 389283885 389316653 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 389283885 389316653).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19731 389283885 389316653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19731)) 389316653 389349421 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 389316653 389349421).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19731 389316653 389349421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19732)) 389349421 389382189 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 389349421 389382189).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19732 389349421 389382189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19733)) 389382189 389414957 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 389382189 389414957).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19733 389382189 389414957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 389283885 389349421).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 389283885 ≤ 389316653)
    (by decide : 389316653 ≤ 389349421) block0 block1

theorem join_0_1 : (twinPrimeSegment 389349421 389414957).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 389349421 ≤ 389382189)
    (by decide : 389382189 ≤ 389414957) block2 block3

theorem join_1_0 : (twinPrimeSegment 389283885 389414957).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 389283885 ≤ 389349421)
    (by decide : 389349421 ≤ 389414957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 389283885 389414957).card = 442 := join_1_0

end S185C10
end Sude.GeneratedTwinScan
