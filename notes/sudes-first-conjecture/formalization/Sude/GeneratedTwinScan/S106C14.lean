import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14972)) 224133165 224165933 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224133165 224165933).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14972 224133165 224165933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14973)) 224165933 224198701 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224165933 224198701).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14973 224165933 224198701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14974)) 224198701 224231469 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224198701 224231469).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14974 224198701 224231469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14975)) 224231469 224264237 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 224231469 224264237).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14975 224231469 224264237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224133165 224198701).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 224133165 ≤ 224165933)
    (by decide : 224165933 ≤ 224198701) block0 block1

theorem join_0_1 : (twinPrimeSegment 224198701 224264237).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 224198701 ≤ 224231469)
    (by decide : 224231469 ≤ 224264237) block2 block3

theorem join_1_0 : (twinPrimeSegment 224133165 224264237).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 224133165 ≤ 224198701)
    (by decide : 224198701 ≤ 224264237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224133165 224264237).card = 486 := join_1_0

end S106C14
end Sude.GeneratedTwinScan
