import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19554)) 382337069 382369837 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382337069 382369837).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19554 382337069 382369837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19555)) 382369837 382402605 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382369837 382402605).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19555 382369837 382402605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19555)) 382402605 382435373 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382402605 382435373).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19555 382402605 382435373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19556)) 382435373 382468141 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382435373 382468141).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19556 382435373 382468141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382337069 382402605).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 382337069 ≤ 382369837)
    (by decide : 382369837 ≤ 382402605) block0 block1

theorem join_0_1 : (twinPrimeSegment 382402605 382468141).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 382402605 ≤ 382435373)
    (by decide : 382435373 ≤ 382468141) block2 block3

theorem join_1_0 : (twinPrimeSegment 382337069 382468141).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 382337069 ≤ 382402605)
    (by decide : 382402605 ≤ 382468141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382337069 382468141).card = 443 := join_1_0

end S182C05
end Sude.GeneratedTwinScan
