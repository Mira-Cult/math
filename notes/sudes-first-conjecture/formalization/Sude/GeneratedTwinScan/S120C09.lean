import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15901)) 252837933 252870701 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252837933 252870701).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15901 252837933 252870701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15902)) 252870701 252903469 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 252870701 252903469).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15902 252870701 252903469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15903)) 252903469 252936237 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 252903469 252936237).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15903 252903469 252936237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15904)) 252936237 252969005 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252936237 252969005).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15904 252936237 252969005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252837933 252903469).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 252837933 ≤ 252870701)
    (by decide : 252870701 ≤ 252903469) block0 block1

theorem join_0_1 : (twinPrimeSegment 252903469 252969005).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 252903469 ≤ 252936237)
    (by decide : 252936237 ≤ 252969005) block2 block3

theorem join_1_0 : (twinPrimeSegment 252837933 252969005).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 252837933 ≤ 252903469)
    (by decide : 252903469 ≤ 252969005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252837933 252969005).card = 455 := join_1_0

end S120C09
end Sude.GeneratedTwinScan
