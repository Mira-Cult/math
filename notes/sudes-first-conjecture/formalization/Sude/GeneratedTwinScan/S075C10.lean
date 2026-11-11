import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12594)) 158597165 158629933 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158597165 158629933).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12594 158597165 158629933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12596)) 158629933 158662701 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158629933 158662701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12596 158629933 158662701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12597)) 158662701 158695469 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158662701 158695469).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12597 158662701 158695469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12598)) 158695469 158728237 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158695469 158728237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12598 158695469 158728237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158597165 158662701).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 158597165 ≤ 158629933)
    (by decide : 158629933 ≤ 158662701) block0 block1

theorem join_0_1 : (twinPrimeSegment 158662701 158728237).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 158662701 ≤ 158695469)
    (by decide : 158695469 ≤ 158728237) block2 block3

theorem join_1_0 : (twinPrimeSegment 158597165 158728237).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 158597165 ≤ 158662701)
    (by decide : 158662701 ≤ 158728237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158597165 158728237).card = 449 := join_1_0

end S075C10
end Sude.GeneratedTwinScan
