import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15437)) 238288941 238321709 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238288941 238321709).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15437 238288941 238321709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15438)) 238321709 238354477 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238321709 238354477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15438 238321709 238354477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15439)) 238354477 238387245 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238354477 238387245).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15439 238354477 238387245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15440)) 238387245 238420013 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238387245 238420013).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15440 238387245 238420013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238288941 238354477).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 238288941 ≤ 238321709)
    (by decide : 238321709 ≤ 238354477) block0 block1

theorem join_0_1 : (twinPrimeSegment 238354477 238420013).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 238354477 ≤ 238387245)
    (by decide : 238387245 ≤ 238420013) block2 block3

theorem join_1_0 : (twinPrimeSegment 238288941 238420013).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 238288941 ≤ 238354477)
    (by decide : 238354477 ≤ 238420013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238288941 238420013).card = 460 := join_1_0

end S113C10
end Sude.GeneratedTwinScan
