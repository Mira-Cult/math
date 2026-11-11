import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16658)) 277479469 277512237 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277479469 277512237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16658 277479469 277512237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16659)) 277512237 277545005 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277512237 277545005).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16659 277512237 277545005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16660)) 277545005 277577773 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277545005 277577773).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16660 277545005 277577773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16661)) 277577773 277610541 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277577773 277610541).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16661 277577773 277610541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277479469 277545005).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 277479469 ≤ 277512237)
    (by decide : 277512237 ≤ 277545005) block0 block1

theorem join_0_1 : (twinPrimeSegment 277545005 277610541).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 277545005 ≤ 277577773)
    (by decide : 277577773 ≤ 277610541) block2 block3

theorem join_1_0 : (twinPrimeSegment 277479469 277610541).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 277479469 ≤ 277545005)
    (by decide : 277545005 ≤ 277610541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277479469 277610541).card = 475 := join_1_0

end S132C05
end Sude.GeneratedTwinScan
