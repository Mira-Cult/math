import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13858)) 192020525 192053293 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192020525 192053293).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13858 192020525 192053293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13859)) 192053293 192086061 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192053293 192086061).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13859 192053293 192086061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13860)) 192086061 192118829 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192086061 192118829).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13860 192086061 192118829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13861)) 192118829 192151597 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192118829 192151597).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13861 192118829 192151597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192020525 192086061).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 192020525 ≤ 192053293)
    (by decide : 192053293 ≤ 192086061) block0 block1

theorem join_0_1 : (twinPrimeSegment 192086061 192151597).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 192086061 ≤ 192118829)
    (by decide : 192118829 ≤ 192151597) block2 block3

theorem join_1_0 : (twinPrimeSegment 192020525 192151597).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 192020525 ≤ 192086061)
    (by decide : 192086061 ≤ 192151597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192020525 192151597).card = 461 := join_1_0

end S091C09
end Sude.GeneratedTwinScan
