import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13069)) 170786861 170819629 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170786861 170819629).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13069 170786861 170819629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13071)) 170819629 170852397 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170819629 170852397).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13071 170819629 170852397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13072)) 170852397 170885165 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170852397 170885165).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13072 170852397 170885165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13073)) 170885165 170917933 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170885165 170917933).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13073 170885165 170917933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170786861 170852397).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 170786861 ≤ 170819629)
    (by decide : 170819629 ≤ 170852397) block0 block1

theorem join_0_1 : (twinPrimeSegment 170852397 170917933).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 170852397 ≤ 170885165)
    (by decide : 170885165 ≤ 170917933) block2 block3

theorem join_1_0 : (twinPrimeSegment 170786861 170917933).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 170786861 ≤ 170852397)
    (by decide : 170852397 ≤ 170917933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170786861 170917933).card = 499 := join_1_0

end S081C07
end Sude.GeneratedTwinScan
