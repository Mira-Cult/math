import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14818)) 219545645 219578413 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219545645 219578413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14818 219545645 219578413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14819)) 219578413 219611181 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219578413 219611181).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14819 219578413 219611181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14820)) 219611181 219643949 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219611181 219643949).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14820 219611181 219643949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14821)) 219643949 219676717 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219643949 219676717).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14821 219643949 219676717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219545645 219611181).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 219545645 ≤ 219578413)
    (by decide : 219578413 ≤ 219611181) block0 block1

theorem join_0_1 : (twinPrimeSegment 219611181 219676717).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 219611181 ≤ 219643949)
    (by decide : 219643949 ≤ 219676717) block2 block3

theorem join_1_0 : (twinPrimeSegment 219545645 219676717).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 219545645 ≤ 219611181)
    (by decide : 219611181 ≤ 219676717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219545645 219676717).card = 442 := join_1_0

end S104C11
end Sude.GeneratedTwinScan
