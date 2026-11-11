import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17975)) 323092525 323125293 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323092525 323125293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17975 323092525 323125293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17976)) 323125293 323158061 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323125293 323158061).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17976 323125293 323158061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17977)) 323158061 323190829 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323158061 323190829).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17977 323158061 323190829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17978)) 323190829 323223597 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323190829 323223597).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17978 323190829 323223597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323092525 323158061).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 323092525 ≤ 323125293)
    (by decide : 323125293 ≤ 323158061) block0 block1

theorem join_0_1 : (twinPrimeSegment 323158061 323223597).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 323158061 ≤ 323190829)
    (by decide : 323190829 ≤ 323223597) block2 block3

theorem join_1_0 : (twinPrimeSegment 323092525 323223597).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 323092525 ≤ 323158061)
    (by decide : 323158061 ≤ 323223597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323092525 323223597).card = 444 := join_1_0

end S154C01
end Sude.GeneratedTwinScan
