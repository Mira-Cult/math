import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20339)) 413663277 413696045 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 413663277 413696045).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20339 413663277 413696045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20340)) 413696045 413728813 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 413696045 413728813).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20340 413696045 413728813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20341)) 413728813 413761581 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 413728813 413761581).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20341 413728813 413761581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20341)) 413761581 413794349 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 413761581 413794349).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20341 413761581 413794349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 413663277 413728813).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 413663277 ≤ 413696045)
    (by decide : 413696045 ≤ 413728813) block0 block1

theorem join_0_1 : (twinPrimeSegment 413728813 413794349).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 413728813 ≤ 413761581)
    (by decide : 413761581 ≤ 413794349) block2 block3

theorem join_1_0 : (twinPrimeSegment 413663277 413794349).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 413663277 ≤ 413728813)
    (by decide : 413728813 ≤ 413794349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 413663277 413794349).card = 448 := join_1_0

end S197C04
end Sude.GeneratedTwinScan
