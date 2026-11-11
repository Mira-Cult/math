import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22895)) 524156973 524189741 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 524156973 524189741).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22895 524156973 524189741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22895)) 524189741 524222509 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 524189741 524222509).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22895 524189741 524222509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22896)) 524222509 524255277 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 524222509 524255277).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22896 524222509 524255277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22897)) 524255277 524288045 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 524255277 524288045).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22897 524255277 524288045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 524156973 524222509).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 524156973 ≤ 524189741)
    (by decide : 524189741 ≤ 524222509) block0 block1

theorem join_0_1 : (twinPrimeSegment 524222509 524288045).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 524222509 ≤ 524255277)
    (by decide : 524255277 ≤ 524288045) block2 block3

theorem join_1_0 : (twinPrimeSegment 524156973 524288045).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 524156973 ≤ 524222509)
    (by decide : 524222509 ≤ 524288045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 524156973 524288045).card = 416 := join_1_0

end S249C15
end Sude.GeneratedTwinScan
