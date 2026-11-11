import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21225)) 450494509 450527277 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450494509 450527277).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21225 450494509 450527277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21226)) 450527277 450560045 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450527277 450560045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21226 450527277 450560045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21227)) 450560045 450592813 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450560045 450592813).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21227 450560045 450592813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21227)) 450592813 450625581 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450592813 450625581).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21227 450592813 450625581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450494509 450560045).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 450494509 ≤ 450527277)
    (by decide : 450527277 ≤ 450560045) block0 block1

theorem join_0_1 : (twinPrimeSegment 450560045 450625581).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 450560045 ≤ 450592813)
    (by decide : 450592813 ≤ 450625581) block2 block3

theorem join_1_0 : (twinPrimeSegment 450494509 450625581).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 450494509 ≤ 450560045)
    (by decide : 450560045 ≤ 450625581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450494509 450625581).card = 432 := join_1_0

end S214C13
end Sude.GeneratedTwinScan
