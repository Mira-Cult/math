import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19794)) 391774253 391807021 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 391774253 391807021).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19794 391774253 391807021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19794)) 391807021 391839789 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 391807021 391839789).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19794 391807021 391839789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19795)) 391839789 391872557 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 391839789 391872557).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19795 391839789 391872557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19796)) 391872557 391905325 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 391872557 391905325).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19796 391872557 391905325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 391774253 391839789).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 391774253 ≤ 391807021)
    (by decide : 391807021 ≤ 391839789) block0 block1

theorem join_0_1 : (twinPrimeSegment 391839789 391905325).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 391839789 ≤ 391872557)
    (by decide : 391872557 ≤ 391905325) block2 block3

theorem join_1_0 : (twinPrimeSegment 391774253 391905325).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 391774253 ≤ 391839789)
    (by decide : 391839789 ≤ 391905325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 391774253 391905325).card = 474 := join_1_0

end S186C13
end Sude.GeneratedTwinScan
