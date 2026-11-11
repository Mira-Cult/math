import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12867)) 165543981 165576749 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165543981 165576749).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12867 165543981 165576749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12868)) 165576749 165609517 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165576749 165609517).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12868 165576749 165609517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12870)) 165609517 165642285 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165609517 165642285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12870 165609517 165642285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12871)) 165642285 165675053 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165642285 165675053).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12871 165642285 165675053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165543981 165609517).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 165543981 ≤ 165576749)
    (by decide : 165576749 ≤ 165609517) block0 block1

theorem join_0_1 : (twinPrimeSegment 165609517 165675053).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 165609517 ≤ 165642285)
    (by decide : 165642285 ≤ 165675053) block2 block3

theorem join_1_0 : (twinPrimeSegment 165543981 165675053).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 165543981 ≤ 165609517)
    (by decide : 165609517 ≤ 165675053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165543981 165675053).card = 465 := join_1_0

end S078C15
end Sude.GeneratedTwinScan
