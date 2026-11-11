import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20659)) 426770477 426803245 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 426770477 426803245).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20659 426770477 426803245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20660)) 426803245 426836013 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426803245 426836013).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20660 426803245 426836013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20660)) 426836013 426868781 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426836013 426868781).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20660 426836013 426868781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20661)) 426868781 426901549 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426868781 426901549).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20661 426868781 426901549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 426770477 426836013).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 426770477 ≤ 426803245)
    (by decide : 426803245 ≤ 426836013) block0 block1

theorem join_0_1 : (twinPrimeSegment 426836013 426901549).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 426836013 ≤ 426868781)
    (by decide : 426868781 ≤ 426901549) block2 block3

theorem join_1_0 : (twinPrimeSegment 426770477 426901549).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 426770477 ≤ 426836013)
    (by decide : 426836013 ≤ 426901549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 426770477 426901549).card = 402 := join_1_0

end S203C08
end Sude.GeneratedTwinScan
