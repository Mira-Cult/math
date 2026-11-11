import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22188)) 492306477 492339245 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492306477 492339245).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22188 492306477 492339245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22189)) 492339245 492372013 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492339245 492372013).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22189 492339245 492372013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22190)) 492372013 492404781 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492372013 492404781).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22190 492372013 492404781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22190)) 492404781 492437549 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492404781 492437549).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22190 492404781 492437549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492306477 492372013).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 492306477 ≤ 492339245)
    (by decide : 492339245 ≤ 492372013) block0 block1

theorem join_0_1 : (twinPrimeSegment 492372013 492437549).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 492372013 ≤ 492404781)
    (by decide : 492404781 ≤ 492437549) block2 block3

theorem join_1_0 : (twinPrimeSegment 492306477 492437549).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 492306477 ≤ 492372013)
    (by decide : 492372013 ≤ 492437549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492306477 492437549).card = 425 := join_1_0

end S234C12
end Sude.GeneratedTwinScan
