import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13229)) 174981165 175013933 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174981165 175013933).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13229 174981165 175013933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13230)) 175013933 175046701 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 175013933 175046701).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13230 175013933 175046701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13231)) 175046701 175079469 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 175046701 175079469).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13231 175046701 175079469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13232)) 175079469 175112237 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 175079469 175112237).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13232 175079469 175112237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174981165 175046701).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 174981165 ≤ 175013933)
    (by decide : 175013933 ≤ 175046701) block0 block1

theorem join_0_1 : (twinPrimeSegment 175046701 175112237).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 175046701 ≤ 175079469)
    (by decide : 175079469 ≤ 175112237) block2 block3

theorem join_1_0 : (twinPrimeSegment 174981165 175112237).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 174981165 ≤ 175046701)
    (by decide : 175046701 ≤ 175112237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174981165 175112237).card = 489 := join_1_0

end S083C07
end Sude.GeneratedTwinScan
