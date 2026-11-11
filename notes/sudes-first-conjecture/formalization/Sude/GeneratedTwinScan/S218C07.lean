import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21403)) 458096685 458129453 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458096685 458129453).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21403 458096685 458129453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21404)) 458129453 458162221 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458129453 458162221).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21404 458129453 458162221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21405)) 458162221 458194989 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458162221 458194989).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21405 458162221 458194989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21406)) 458194989 458227757 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458194989 458227757).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21406 458194989 458227757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458096685 458162221).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 458096685 ≤ 458129453)
    (by decide : 458129453 ≤ 458162221) block0 block1

theorem join_0_1 : (twinPrimeSegment 458162221 458227757).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 458162221 ≤ 458194989)
    (by decide : 458194989 ≤ 458227757) block2 block3

theorem join_1_0 : (twinPrimeSegment 458096685 458227757).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 458096685 ≤ 458162221)
    (by decide : 458162221 ≤ 458227757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458096685 458227757).card = 434 := join_1_0

end S218C07
end Sude.GeneratedTwinScan
