import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20722)) 429391917 429424685 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429391917 429424685).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20722 429391917 429424685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20723)) 429424685 429457453 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429424685 429457453).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20723 429424685 429457453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20724)) 429457453 429490221 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429457453 429490221).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20724 429457453 429490221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20724)) 429490221 429522989 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429490221 429522989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20724 429490221 429522989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429391917 429457453).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 429391917 ≤ 429424685)
    (by decide : 429424685 ≤ 429457453) block0 block1

theorem join_0_1 : (twinPrimeSegment 429457453 429522989).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 429457453 ≤ 429490221)
    (by decide : 429490221 ≤ 429522989) block2 block3

theorem join_1_0 : (twinPrimeSegment 429391917 429522989).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 429391917 ≤ 429457453)
    (by decide : 429457453 ≤ 429522989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429391917 429522989).card = 441 := join_1_0

end S204C12
end Sude.GeneratedTwinScan
