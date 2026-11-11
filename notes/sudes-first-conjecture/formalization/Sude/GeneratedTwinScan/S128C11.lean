import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16428)) 269877293 269910061 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269877293 269910061).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16428 269877293 269910061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16429)) 269910061 269942829 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269910061 269942829).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16429 269910061 269942829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16430)) 269942829 269975597 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269942829 269975597).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16430 269942829 269975597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16431)) 269975597 270008365 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269975597 270008365).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16431 269975597 270008365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269877293 269942829).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 269877293 ≤ 269910061)
    (by decide : 269910061 ≤ 269942829) block0 block1

theorem join_0_1 : (twinPrimeSegment 269942829 270008365).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 269942829 ≤ 269975597)
    (by decide : 269975597 ≤ 270008365) block2 block3

theorem join_1_0 : (twinPrimeSegment 269877293 270008365).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 269877293 ≤ 269942829)
    (by decide : 269942829 ≤ 270008365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269877293 270008365).card = 462 := join_1_0

end S128C11
end Sude.GeneratedTwinScan
