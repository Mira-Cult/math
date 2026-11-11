import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17968)) 322830381 322863149 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 322830381 322863149).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17968 322830381 322863149
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17969)) 322863149 322895917 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 322863149 322895917).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17969 322863149 322895917
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17970)) 322895917 322928685 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 322895917 322928685).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17970 322895917 322928685
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17971)) 322928685 322961453 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 322928685 322961453).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17971 322928685 322961453
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 322830381 322895917).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 322830381 ≤ 322863149)
    (by decide : 322863149 ≤ 322895917) block0 block1

theorem join_0_1 : (twinPrimeSegment 322895917 322961453).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 322895917 ≤ 322928685)
    (by decide : 322928685 ≤ 322961453) block2 block3

theorem join_1_0 : (twinPrimeSegment 322830381 322961453).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 322830381 ≤ 322895917)
    (by decide : 322895917 ≤ 322961453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 322830381 322961453).card = 464 := join_1_0

end S153C15
end Sude.GeneratedTwinScan
