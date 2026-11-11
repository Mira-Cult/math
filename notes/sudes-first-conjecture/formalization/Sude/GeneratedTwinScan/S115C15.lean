import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15593)) 243138605 243171373 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243138605 243171373).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15593 243138605 243171373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15595)) 243171373 243204141 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243171373 243204141).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15595 243171373 243204141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15596)) 243204141 243236909 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243204141 243236909).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15596 243204141 243236909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15597)) 243236909 243269677 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 243236909 243269677).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15597 243236909 243269677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243138605 243204141).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 243138605 ≤ 243171373)
    (by decide : 243171373 ≤ 243204141) block0 block1

theorem join_0_1 : (twinPrimeSegment 243204141 243269677).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 243204141 ≤ 243236909)
    (by decide : 243236909 ≤ 243269677) block2 block3

theorem join_1_0 : (twinPrimeSegment 243138605 243269677).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 243138605 ≤ 243204141)
    (by decide : 243204141 ≤ 243269677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243138605 243269677).card = 464 := join_1_0

end S115C15
end Sude.GeneratedTwinScan
