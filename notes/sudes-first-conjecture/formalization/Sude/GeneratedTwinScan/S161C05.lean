import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18393)) 338296877 338329645 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338296877 338329645).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18393 338296877 338329645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18394)) 338329645 338362413 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338329645 338362413).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18394 338329645 338362413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18395)) 338362413 338395181 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338362413 338395181).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18395 338362413 338395181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18396)) 338395181 338427949 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338395181 338427949).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18396 338395181 338427949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338296877 338362413).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 338296877 ≤ 338329645)
    (by decide : 338329645 ≤ 338362413) block0 block1

theorem join_0_1 : (twinPrimeSegment 338362413 338427949).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 338362413 ≤ 338395181)
    (by decide : 338395181 ≤ 338427949) block2 block3

theorem join_1_0 : (twinPrimeSegment 338296877 338427949).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 338296877 ≤ 338362413)
    (by decide : 338362413 ≤ 338427949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338296877 338427949).card = 458 := join_1_0

end S161C05
end Sude.GeneratedTwinScan
