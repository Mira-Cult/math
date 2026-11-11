import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S101C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14622)) 213778477 213811245 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 213778477 213811245).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14622 213778477 213811245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14623)) 213811245 213844013 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 213811245 213844013).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14623 213811245 213844013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14624)) 213844013 213876781 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 213844013 213876781).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14624 213844013 213876781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14625)) 213876781 213909549 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 213876781 213909549).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14625 213876781 213909549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 213778477 213844013).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 213778477 ≤ 213811245)
    (by decide : 213811245 ≤ 213844013) block0 block1

theorem join_0_1 : (twinPrimeSegment 213844013 213909549).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 213844013 ≤ 213876781)
    (by decide : 213876781 ≤ 213909549) block2 block3

theorem join_1_0 : (twinPrimeSegment 213778477 213909549).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 213778477 ≤ 213844013)
    (by decide : 213844013 ≤ 213909549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 213778477 213909549).card = 457 := join_1_0

end S101C15
end Sude.GeneratedTwinScan
