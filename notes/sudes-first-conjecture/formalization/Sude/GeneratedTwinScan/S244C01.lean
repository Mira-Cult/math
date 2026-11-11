import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22624)) 511836205 511868973 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511836205 511868973).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22624 511836205 511868973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22625)) 511868973 511901741 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511868973 511901741).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22625 511868973 511901741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22625)) 511901741 511934509 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511901741 511934509).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22625 511901741 511934509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22626)) 511934509 511967277 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511934509 511967277).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22626 511934509 511967277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511836205 511901741).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 511836205 ≤ 511868973)
    (by decide : 511868973 ≤ 511901741) block0 block1

theorem join_0_1 : (twinPrimeSegment 511901741 511967277).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 511901741 ≤ 511934509)
    (by decide : 511934509 ≤ 511967277) block2 block3

theorem join_1_0 : (twinPrimeSegment 511836205 511967277).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 511836205 ≤ 511901741)
    (by decide : 511901741 ≤ 511967277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511836205 511967277).card = 419 := join_1_0

end S244C01
end Sude.GeneratedTwinScan
