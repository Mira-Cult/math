import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17810)) 317194285 317227053 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317194285 317227053).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17810 317194285 317227053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17811)) 317227053 317259821 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317227053 317259821).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17811 317227053 317259821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17812)) 317259821 317292589 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317259821 317292589).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17812 317259821 317292589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17813)) 317292589 317325357 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317292589 317325357).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17813 317292589 317325357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317194285 317259821).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 317194285 ≤ 317227053)
    (by decide : 317227053 ≤ 317259821) block0 block1

theorem join_0_1 : (twinPrimeSegment 317259821 317325357).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 317259821 ≤ 317292589)
    (by decide : 317292589 ≤ 317325357) block2 block3

theorem join_1_0 : (twinPrimeSegment 317194285 317325357).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 317194285 ≤ 317259821)
    (by decide : 317259821 ≤ 317325357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317194285 317325357).card = 468 := join_1_0

end S151C04
end Sude.GeneratedTwinScan
