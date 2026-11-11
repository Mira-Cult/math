import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19075)) 363855917 363888685 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363855917 363888685).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19075 363855917 363888685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19076)) 363888685 363921453 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363888685 363921453).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19076 363888685 363921453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19077)) 363921453 363954221 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363921453 363954221).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19077 363921453 363954221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19078)) 363954221 363986989 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363954221 363986989).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19078 363954221 363986989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363855917 363921453).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 363855917 ≤ 363888685)
    (by decide : 363888685 ≤ 363921453) block0 block1

theorem join_0_1 : (twinPrimeSegment 363921453 363986989).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 363921453 ≤ 363954221)
    (by decide : 363954221 ≤ 363986989) block2 block3

theorem join_1_0 : (twinPrimeSegment 363855917 363986989).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 363855917 ≤ 363921453)
    (by decide : 363921453 ≤ 363986989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363855917 363986989).card = 428 := join_1_0

end S173C08
end Sude.GeneratedTwinScan
