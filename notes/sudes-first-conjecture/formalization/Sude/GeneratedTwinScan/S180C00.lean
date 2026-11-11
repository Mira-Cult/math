import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19429)) 377487405 377520173 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377487405 377520173).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19429 377487405 377520173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19430)) 377520173 377552941 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377520173 377552941).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19430 377520173 377552941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19431)) 377552941 377585709 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377552941 377585709).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19431 377552941 377585709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19432)) 377585709 377618477 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377585709 377618477).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19432 377585709 377618477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377487405 377552941).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 377520173)
    (by decide : 377520173 ≤ 377552941) block0 block1

theorem join_0_1 : (twinPrimeSegment 377552941 377618477).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 377552941 ≤ 377585709)
    (by decide : 377585709 ≤ 377618477) block2 block3

theorem join_1_0 : (twinPrimeSegment 377487405 377618477).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 377552941)
    (by decide : 377552941 ≤ 377618477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377487405 377618477).card = 444 := join_1_0

end S180C00
end Sude.GeneratedTwinScan
