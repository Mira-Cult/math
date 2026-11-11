import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20662)) 426901549 426934317 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 426901549 426934317).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20662 426901549 426934317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20663)) 426934317 426967085 = 78 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426934317 426967085).card = 78 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20663 426934317 426967085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20663)) 426967085 426999853 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 426967085 426999853).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20663 426967085 426999853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20664)) 426999853 427032621 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 426999853 427032621).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20664 426999853 427032621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 426901549 426967085).card = 186 := by
  simpa using combineTwinPrimeSegments (by decide : 426901549 ≤ 426934317)
    (by decide : 426934317 ≤ 426967085) block0 block1

theorem join_0_1 : (twinPrimeSegment 426967085 427032621).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 426967085 ≤ 426999853)
    (by decide : 426999853 ≤ 427032621) block2 block3

theorem join_1_0 : (twinPrimeSegment 426901549 427032621).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 426901549 ≤ 426967085)
    (by decide : 426967085 ≤ 427032621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 426901549 427032621).card = 398 := join_1_0

end S203C09
end Sude.GeneratedTwinScan
