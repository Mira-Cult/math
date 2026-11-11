import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14217)) 202113069 202145837 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202113069 202145837).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14217 202113069 202145837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14218)) 202145837 202178605 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202145837 202178605).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14218 202145837 202178605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14220)) 202178605 202211373 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202178605 202211373).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14220 202178605 202211373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14221)) 202211373 202244141 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202211373 202244141).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14221 202211373 202244141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202113069 202178605).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 202113069 ≤ 202145837)
    (by decide : 202145837 ≤ 202178605) block0 block1

theorem join_0_1 : (twinPrimeSegment 202178605 202244141).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 202178605 ≤ 202211373)
    (by decide : 202211373 ≤ 202244141) block2 block3

theorem join_1_0 : (twinPrimeSegment 202113069 202244141).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 202113069 ≤ 202178605)
    (by decide : 202178605 ≤ 202244141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202113069 202244141).card = 464 := join_1_0

end S096C06
end Sude.GeneratedTwinScan
