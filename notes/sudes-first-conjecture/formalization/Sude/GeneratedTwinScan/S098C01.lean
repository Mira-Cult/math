import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14341)) 205652013 205684781 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205652013 205684781).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14341 205652013 205684781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14342)) 205684781 205717549 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205684781 205717549).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14342 205684781 205717549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14343)) 205717549 205750317 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205717549 205750317).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14343 205717549 205750317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14345)) 205750317 205783085 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205750317 205783085).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14345 205750317 205783085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205652013 205717549).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 205652013 ≤ 205684781)
    (by decide : 205684781 ≤ 205717549) block0 block1

theorem join_0_1 : (twinPrimeSegment 205717549 205783085).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 205717549 ≤ 205750317)
    (by decide : 205750317 ≤ 205783085) block2 block3

theorem join_1_0 : (twinPrimeSegment 205652013 205783085).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 205652013 ≤ 205717549)
    (by decide : 205717549 ≤ 205783085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205652013 205783085).card = 465 := join_1_0

end S098C01
end Sude.GeneratedTwinScan
