import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13479)) 181665837 181698605 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181665837 181698605).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13479 181665837 181698605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13480)) 181698605 181731373 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181698605 181731373).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13480 181698605 181731373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13481)) 181731373 181764141 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181731373 181764141).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13481 181731373 181764141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13483)) 181764141 181796909 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181764141 181796909).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13483 181764141 181796909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181665837 181731373).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 181665837 ≤ 181698605)
    (by decide : 181698605 ≤ 181731373) block0 block1

theorem join_0_1 : (twinPrimeSegment 181731373 181796909).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 181731373 ≤ 181764141)
    (by decide : 181764141 ≤ 181796909) block2 block3

theorem join_1_0 : (twinPrimeSegment 181665837 181796909).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 181665837 ≤ 181731373)
    (by decide : 181731373 ≤ 181796909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181665837 181796909).card = 479 := join_1_0

end S086C10
end Sude.GeneratedTwinScan
