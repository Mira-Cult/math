import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15429)) 238026797 238059565 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 238026797 238059565).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15429 238026797 238059565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15430)) 238059565 238092333 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 238059565 238092333).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15430 238059565 238092333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15431)) 238092333 238125101 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 238092333 238125101).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15431 238092333 238125101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15432)) 238125101 238157869 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 238125101 238157869).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15432 238125101 238157869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 238026797 238092333).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 238026797 ≤ 238059565)
    (by decide : 238059565 ≤ 238092333) block0 block1

theorem join_0_1 : (twinPrimeSegment 238092333 238157869).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 238092333 ≤ 238125101)
    (by decide : 238125101 ≤ 238157869) block2 block3

theorem join_1_0 : (twinPrimeSegment 238026797 238157869).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 238026797 ≤ 238092333)
    (by decide : 238092333 ≤ 238157869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 238026797 238157869).card = 501 := join_1_0

end S113C08
end Sude.GeneratedTwinScan
