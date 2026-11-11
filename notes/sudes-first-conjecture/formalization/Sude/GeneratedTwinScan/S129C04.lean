import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16464)) 271056941 271089709 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 271056941 271089709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16464 271056941 271089709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16465)) 271089709 271122477 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 271089709 271122477).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16465 271089709 271122477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16466)) 271122477 271155245 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 271122477 271155245).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16466 271122477 271155245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16467)) 271155245 271188013 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 271155245 271188013).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16467 271155245 271188013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 271056941 271122477).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 271056941 ≤ 271089709)
    (by decide : 271089709 ≤ 271122477) block0 block1

theorem join_0_1 : (twinPrimeSegment 271122477 271188013).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 271122477 ≤ 271155245)
    (by decide : 271155245 ≤ 271188013) block2 block3

theorem join_1_0 : (twinPrimeSegment 271056941 271188013).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 271056941 ≤ 271122477)
    (by decide : 271122477 ≤ 271188013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 271056941 271188013).card = 432 := join_1_0

end S129C04
end Sude.GeneratedTwinScan
