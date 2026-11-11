import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14857)) 220725293 220758061 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220725293 220758061).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14857 220725293 220758061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14859)) 220758061 220790829 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220758061 220790829).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14859 220758061 220790829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14860)) 220790829 220823597 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220790829 220823597).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14860 220790829 220823597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14861)) 220823597 220856365 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220823597 220856365).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14861 220823597 220856365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220725293 220790829).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 220725293 ≤ 220758061)
    (by decide : 220758061 ≤ 220790829) block0 block1

theorem join_0_1 : (twinPrimeSegment 220790829 220856365).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 220790829 ≤ 220823597)
    (by decide : 220823597 ≤ 220856365) block2 block3

theorem join_1_0 : (twinPrimeSegment 220725293 220856365).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 220725293 ≤ 220790829)
    (by decide : 220790829 ≤ 220856365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220725293 220856365).card = 450 := join_1_0

end S105C04
end Sude.GeneratedTwinScan
