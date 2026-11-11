import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16850)) 283901997 283934765 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 283901997 283934765).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16850 283901997 283934765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16851)) 283934765 283967533 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 283934765 283967533).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16851 283934765 283967533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16852)) 283967533 284000301 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 283967533 284000301).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16852 283967533 284000301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16853)) 284000301 284033069 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284000301 284033069).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16853 284000301 284033069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 283901997 283967533).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 283901997 ≤ 283934765)
    (by decide : 283934765 ≤ 283967533) block0 block1

theorem join_0_1 : (twinPrimeSegment 283967533 284033069).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 283967533 ≤ 284000301)
    (by decide : 284000301 ≤ 284033069) block2 block3

theorem join_1_0 : (twinPrimeSegment 283901997 284033069).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 283901997 ≤ 283967533)
    (by decide : 283967533 ≤ 284033069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 283901997 284033069).card = 428 := join_1_0

end S135C06
end Sude.GeneratedTwinScan
