import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S213C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21151)) 447348781 447381549 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 447348781 447381549).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21151 447348781 447381549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21152)) 447381549 447414317 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 447381549 447414317).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21152 447381549 447414317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21152)) 447414317 447447085 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 447414317 447447085).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21152 447414317 447447085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21153)) 447447085 447479853 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 447447085 447479853).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21153 447447085 447479853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 447348781 447414317).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 447348781 ≤ 447381549)
    (by decide : 447381549 ≤ 447414317) block0 block1

theorem join_0_1 : (twinPrimeSegment 447414317 447479853).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 447414317 ≤ 447447085)
    (by decide : 447447085 ≤ 447479853) block2 block3

theorem join_1_0 : (twinPrimeSegment 447348781 447479853).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 447348781 ≤ 447414317)
    (by decide : 447414317 ≤ 447479853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 447348781 447479853).card = 455 := join_1_0

end S213C05
end Sude.GeneratedTwinScan
