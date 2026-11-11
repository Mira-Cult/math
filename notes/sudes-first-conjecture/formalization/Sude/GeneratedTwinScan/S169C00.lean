import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18826)) 354418733 354451501 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354418733 354451501).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18826 354418733 354451501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18827)) 354451501 354484269 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354451501 354484269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18827 354451501 354484269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18828)) 354484269 354517037 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 354484269 354517037).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18828 354484269 354517037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18829)) 354517037 354549805 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 354517037 354549805).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18829 354517037 354549805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354418733 354484269).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 354451501)
    (by decide : 354451501 ≤ 354484269) block0 block1

theorem join_0_1 : (twinPrimeSegment 354484269 354549805).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 354484269 ≤ 354517037)
    (by decide : 354517037 ≤ 354549805) block2 block3

theorem join_1_0 : (twinPrimeSegment 354418733 354549805).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 354418733 ≤ 354484269)
    (by decide : 354484269 ≤ 354549805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354418733 354549805).card = 449 := join_1_0

end S169C00
end Sude.GeneratedTwinScan
