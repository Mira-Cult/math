import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18315)) 335413293 335446061 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335413293 335446061).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18315 335413293 335446061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18316)) 335446061 335478829 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335446061 335478829).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18316 335446061 335478829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18316)) 335478829 335511597 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335478829 335511597).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18316 335478829 335511597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18317)) 335511597 335544365 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335511597 335544365).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18317 335511597 335544365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335413293 335478829).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 335413293 ≤ 335446061)
    (by decide : 335446061 ≤ 335478829) block0 block1

theorem join_0_1 : (twinPrimeSegment 335478829 335544365).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 335478829 ≤ 335511597)
    (by decide : 335511597 ≤ 335544365) block2 block3

theorem join_1_0 : (twinPrimeSegment 335413293 335544365).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 335413293 ≤ 335478829)
    (by decide : 335478829 ≤ 335544365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335413293 335544365).card = 430 := join_1_0

end S159C15
end Sude.GeneratedTwinScan
