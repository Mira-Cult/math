import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14910)) 222298157 222330925 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222298157 222330925).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14910 222298157 222330925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14911)) 222330925 222363693 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222330925 222363693).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14911 222330925 222363693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14912)) 222363693 222396461 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222363693 222396461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14912 222363693 222396461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14914)) 222396461 222429229 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222396461 222429229).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14914 222396461 222429229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222298157 222363693).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 222330925)
    (by decide : 222330925 ≤ 222363693) block0 block1

theorem join_0_1 : (twinPrimeSegment 222363693 222429229).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 222363693 ≤ 222396461)
    (by decide : 222396461 ≤ 222429229) block2 block3

theorem join_1_0 : (twinPrimeSegment 222298157 222429229).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 222363693)
    (by decide : 222363693 ≤ 222429229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222298157 222429229).card = 458 := join_1_0

end S106C00
end Sude.GeneratedTwinScan
