import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13581)) 184418349 184451117 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184418349 184451117).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13581 184418349 184451117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13582)) 184451117 184483885 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184451117 184483885).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13582 184451117 184483885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13583)) 184483885 184516653 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 184483885 184516653).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13583 184483885 184516653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13584)) 184516653 184549421 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 184516653 184549421).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13584 184516653 184549421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184418349 184483885).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 184418349 ≤ 184451117)
    (by decide : 184451117 ≤ 184483885) block0 block1

theorem join_0_1 : (twinPrimeSegment 184483885 184549421).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 184483885 ≤ 184516653)
    (by decide : 184516653 ≤ 184549421) block2 block3

theorem join_1_0 : (twinPrimeSegment 184418349 184549421).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 184418349 ≤ 184483885)
    (by decide : 184483885 ≤ 184549421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184418349 184549421).card = 502 := join_1_0

end S087C15
end Sude.GeneratedTwinScan
