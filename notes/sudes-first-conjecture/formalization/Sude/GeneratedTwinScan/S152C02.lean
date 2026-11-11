import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17862)) 319029293 319062061 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319029293 319062061).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17862 319029293 319062061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17863)) 319062061 319094829 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319062061 319094829).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17863 319062061 319094829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17864)) 319094829 319127597 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 319094829 319127597).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17864 319094829 319127597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17865)) 319127597 319160365 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 319127597 319160365).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17865 319127597 319160365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319029293 319094829).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 319029293 ≤ 319062061)
    (by decide : 319062061 ≤ 319094829) block0 block1

theorem join_0_1 : (twinPrimeSegment 319094829 319160365).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 319094829 ≤ 319127597)
    (by decide : 319127597 ≤ 319160365) block2 block3

theorem join_1_0 : (twinPrimeSegment 319029293 319160365).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 319029293 ≤ 319094829)
    (by decide : 319094829 ≤ 319160365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319029293 319160365).card = 436 := join_1_0

end S152C02
end Sude.GeneratedTwinScan
