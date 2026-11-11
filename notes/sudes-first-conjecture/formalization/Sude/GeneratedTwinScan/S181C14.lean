import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19530)) 381419565 381452333 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381419565 381452333).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19530 381419565 381452333
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19531)) 381452333 381485101 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381452333 381485101).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19531 381452333 381485101
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19532)) 381485101 381517869 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 381485101 381517869).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19532 381485101 381517869
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19533)) 381517869 381550637 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 381517869 381550637).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19533 381517869 381550637
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381419565 381485101).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 381419565 ≤ 381452333)
    (by decide : 381452333 ≤ 381485101) block0 block1

theorem join_0_1 : (twinPrimeSegment 381485101 381550637).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 381485101 ≤ 381517869)
    (by decide : 381517869 ≤ 381550637) block2 block3

theorem join_1_0 : (twinPrimeSegment 381419565 381550637).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 381419565 ≤ 381485101)
    (by decide : 381485101 ≤ 381550637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381419565 381550637).card = 449 := join_1_0

end S181C14
end Sude.GeneratedTwinScan
