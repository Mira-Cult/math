import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21813)) 475791405 475824173 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 475791405 475824173).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21813 475791405 475824173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21814)) 475824173 475856941 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 475824173 475856941).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21814 475824173 475856941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21814)) 475856941 475889709 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 475856941 475889709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21814 475856941 475889709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21815)) 475889709 475922477 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 475889709 475922477).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21815 475889709 475922477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 475791405 475856941).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 475791405 ≤ 475824173)
    (by decide : 475824173 ≤ 475856941) block0 block1

theorem join_0_1 : (twinPrimeSegment 475856941 475922477).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 475856941 ≤ 475889709)
    (by decide : 475889709 ≤ 475922477) block2 block3

theorem join_1_0 : (twinPrimeSegment 475791405 475922477).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 475791405 ≤ 475856941)
    (by decide : 475856941 ≤ 475922477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 475791405 475922477).card = 451 := join_1_0

end S226C14
end Sude.GeneratedTwinScan
