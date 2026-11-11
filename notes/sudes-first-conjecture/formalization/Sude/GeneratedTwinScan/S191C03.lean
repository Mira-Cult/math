import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20024)) 400949293 400982061 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400949293 400982061).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20024 400949293 400982061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20025)) 400982061 401014829 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400982061 401014829).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20025 400982061 401014829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20026)) 401014829 401047597 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401014829 401047597).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20026 401014829 401047597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20026)) 401047597 401080365 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401047597 401080365).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20026 401047597 401080365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400949293 401014829).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 400949293 ≤ 400982061)
    (by decide : 400982061 ≤ 401014829) block0 block1

theorem join_0_1 : (twinPrimeSegment 401014829 401080365).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 401014829 ≤ 401047597)
    (by decide : 401047597 ≤ 401080365) block2 block3

theorem join_1_0 : (twinPrimeSegment 400949293 401080365).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 400949293 ≤ 401014829)
    (by decide : 401014829 ≤ 401080365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400949293 401080365).card = 447 := join_1_0

end S191C03
end Sude.GeneratedTwinScan
