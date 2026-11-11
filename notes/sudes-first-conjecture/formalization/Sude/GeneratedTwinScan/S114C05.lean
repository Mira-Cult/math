import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15484)) 239730733 239763501 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239730733 239763501).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15484 239730733 239763501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15485)) 239763501 239796269 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239763501 239796269).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15485 239763501 239796269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15486)) 239796269 239829037 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239796269 239829037).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15486 239796269 239829037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15487)) 239829037 239861805 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239829037 239861805).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15487 239829037 239861805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239730733 239796269).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 239730733 ≤ 239763501)
    (by decide : 239763501 ≤ 239796269) block0 block1

theorem join_0_1 : (twinPrimeSegment 239796269 239861805).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 239796269 ≤ 239829037)
    (by decide : 239829037 ≤ 239861805) block2 block3

theorem join_1_0 : (twinPrimeSegment 239730733 239861805).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 239730733 ≤ 239796269)
    (by decide : 239796269 ≤ 239861805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239730733 239861805).card = 436 := join_1_0

end S114C05
end Sude.GeneratedTwinScan
