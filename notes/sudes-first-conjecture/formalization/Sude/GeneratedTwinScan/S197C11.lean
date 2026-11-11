import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S197C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20362)) 414580781 414613549 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 414580781 414613549).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20362 414580781 414613549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20362)) 414613549 414646317 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 414613549 414646317).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20362 414613549 414646317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20363)) 414646317 414679085 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 414646317 414679085).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20363 414646317 414679085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20364)) 414679085 414711853 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 414679085 414711853).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20364 414679085 414711853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 414580781 414646317).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 414580781 ≤ 414613549)
    (by decide : 414613549 ≤ 414646317) block0 block1

theorem join_0_1 : (twinPrimeSegment 414646317 414711853).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 414646317 ≤ 414679085)
    (by decide : 414679085 ≤ 414711853) block2 block3

theorem join_1_0 : (twinPrimeSegment 414580781 414711853).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 414580781 ≤ 414646317)
    (by decide : 414646317 ≤ 414711853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 414580781 414711853).card = 415 := join_1_0

end S197C11
end Sude.GeneratedTwinScan
