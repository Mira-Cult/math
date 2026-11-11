import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16012)) 256376877 256409645 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256376877 256409645).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16012 256376877 256409645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16013)) 256409645 256442413 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256409645 256442413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16013 256409645 256442413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16014)) 256442413 256475181 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256442413 256475181).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16014 256442413 256475181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16015)) 256475181 256507949 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256475181 256507949).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16015 256475181 256507949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256376877 256442413).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 256376877 ≤ 256409645)
    (by decide : 256409645 ≤ 256442413) block0 block1

theorem join_0_1 : (twinPrimeSegment 256442413 256507949).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 256442413 ≤ 256475181)
    (by decide : 256475181 ≤ 256507949) block2 block3

theorem join_1_0 : (twinPrimeSegment 256376877 256507949).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 256376877 ≤ 256442413)
    (by decide : 256442413 ≤ 256507949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256376877 256507949).card = 462 := join_1_0

end S122C04
end Sude.GeneratedTwinScan
