import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13532)) 183107629 183140397 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183107629 183140397).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13532 183107629 183140397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13534)) 183140397 183173165 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183140397 183173165).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13534 183140397 183173165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13535)) 183173165 183205933 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183173165 183205933).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13535 183173165 183205933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13536)) 183205933 183238701 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183205933 183238701).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13536 183205933 183238701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183107629 183173165).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 183107629 ≤ 183140397)
    (by decide : 183140397 ≤ 183173165) block0 block1

theorem join_0_1 : (twinPrimeSegment 183173165 183238701).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 183173165 ≤ 183205933)
    (by decide : 183205933 ≤ 183238701) block2 block3

theorem join_1_0 : (twinPrimeSegment 183107629 183238701).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 183107629 ≤ 183173165)
    (by decide : 183173165 ≤ 183238701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183107629 183238701).card = 486 := join_1_0

end S087C05
end Sude.GeneratedTwinScan
