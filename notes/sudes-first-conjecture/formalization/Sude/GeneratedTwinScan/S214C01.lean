import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21188)) 448921645 448954413 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 448921645 448954413).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21188 448921645 448954413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21189)) 448954413 448987181 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 448954413 448987181).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21189 448954413 448987181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21190)) 448987181 449019949 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 448987181 449019949).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21190 448987181 449019949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21190)) 449019949 449052717 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449019949 449052717).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21190 449019949 449052717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 448921645 448987181).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 448921645 ≤ 448954413)
    (by decide : 448954413 ≤ 448987181) block0 block1

theorem join_0_1 : (twinPrimeSegment 448987181 449052717).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 448987181 ≤ 449019949)
    (by decide : 449019949 ≤ 449052717) block2 block3

theorem join_1_0 : (twinPrimeSegment 448921645 449052717).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 448921645 ≤ 448987181)
    (by decide : 448987181 ≤ 449052717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 448921645 449052717).card = 431 := join_1_0

end S214C01
end Sude.GeneratedTwinScan
