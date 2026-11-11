import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21489)) 461766701 461799469 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461766701 461799469).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21489 461766701 461799469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21490)) 461799469 461832237 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461799469 461832237).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21490 461799469 461832237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21491)) 461832237 461865005 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461832237 461865005).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21491 461832237 461865005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21491)) 461865005 461897773 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461865005 461897773).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21491 461865005 461897773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461766701 461832237).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 461766701 ≤ 461799469)
    (by decide : 461799469 ≤ 461832237) block0 block1

theorem join_0_1 : (twinPrimeSegment 461832237 461897773).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 461832237 ≤ 461865005)
    (by decide : 461865005 ≤ 461897773) block2 block3

theorem join_1_0 : (twinPrimeSegment 461766701 461897773).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 461766701 ≤ 461832237)
    (by decide : 461832237 ≤ 461897773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461766701 461897773).card = 440 := join_1_0

end S220C03
end Sude.GeneratedTwinScan
