import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21975)) 482869293 482902061 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 482869293 482902061).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21975 482869293 482902061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21975)) 482902061 482934829 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 482902061 482934829).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21975 482902061 482934829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21976)) 482934829 482967597 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 482934829 482967597).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21976 482934829 482967597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21977)) 482967597 483000365 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 482967597 483000365).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21977 482967597 483000365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 482869293 482934829).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 482869293 ≤ 482902061)
    (by decide : 482902061 ≤ 482934829) block0 block1

theorem join_0_1 : (twinPrimeSegment 482934829 483000365).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 482934829 ≤ 482967597)
    (by decide : 482967597 ≤ 483000365) block2 block3

theorem join_1_0 : (twinPrimeSegment 482869293 483000365).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 482869293 ≤ 482934829)
    (by decide : 482934829 ≤ 483000365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 482869293 483000365).card = 440 := join_1_0

end S230C04
end Sude.GeneratedTwinScan
