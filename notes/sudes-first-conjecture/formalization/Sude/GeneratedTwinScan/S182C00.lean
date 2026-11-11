import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19537)) 381681709 381714477 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381681709 381714477).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19537 381681709 381714477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19538)) 381714477 381747245 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381714477 381747245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19538 381714477 381747245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19539)) 381747245 381780013 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 381747245 381780013).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19539 381747245 381780013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19540)) 381780013 381812781 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 381780013 381812781).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19540 381780013 381812781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381681709 381747245).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 381714477)
    (by decide : 381714477 ≤ 381747245) block0 block1

theorem join_0_1 : (twinPrimeSegment 381747245 381812781).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 381747245 ≤ 381780013)
    (by decide : 381780013 ≤ 381812781) block2 block3

theorem join_1_0 : (twinPrimeSegment 381681709 381812781).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 381747245)
    (by decide : 381747245 ≤ 381812781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381681709 381812781).card = 439 := join_1_0

end S182C00
end Sude.GeneratedTwinScan
