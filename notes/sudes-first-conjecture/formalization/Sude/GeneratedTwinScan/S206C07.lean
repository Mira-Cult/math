import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20807)) 432930861 432963629 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432930861 432963629).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20807 432930861 432963629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20808)) 432963629 432996397 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432963629 432996397).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20808 432963629 432996397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20809)) 432996397 433029165 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432996397 433029165).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20809 432996397 433029165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20810)) 433029165 433061933 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433029165 433061933).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20810 433029165 433061933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432930861 432996397).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 432930861 ≤ 432963629)
    (by decide : 432963629 ≤ 432996397) block0 block1

theorem join_0_1 : (twinPrimeSegment 432996397 433061933).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 432996397 ≤ 433029165)
    (by decide : 433029165 ≤ 433061933) block2 block3

theorem join_1_0 : (twinPrimeSegment 432930861 433061933).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 432930861 ≤ 432996397)
    (by decide : 432996397 ≤ 433061933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432930861 433061933).card = 441 := join_1_0

end S206C07
end Sude.GeneratedTwinScan
