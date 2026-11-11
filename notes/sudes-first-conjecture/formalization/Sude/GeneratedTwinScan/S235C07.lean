import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22221)) 493748269 493781037 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493748269 493781037).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22221 493748269 493781037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22221)) 493781037 493813805 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493781037 493813805).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22221 493781037 493813805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22222)) 493813805 493846573 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493813805 493846573).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22222 493813805 493846573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22223)) 493846573 493879341 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493846573 493879341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22223 493846573 493879341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493748269 493813805).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 493748269 ≤ 493781037)
    (by decide : 493781037 ≤ 493813805) block0 block1

theorem join_0_1 : (twinPrimeSegment 493813805 493879341).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 493813805 ≤ 493846573)
    (by decide : 493846573 ≤ 493879341) block2 block3

theorem join_1_0 : (twinPrimeSegment 493748269 493879341).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 493748269 ≤ 493813805)
    (by decide : 493813805 ≤ 493879341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493748269 493879341).card = 413 := join_1_0

end S235C07
end Sude.GeneratedTwinScan
