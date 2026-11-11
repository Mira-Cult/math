import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21611)) 467009581 467042349 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467009581 467042349).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21611 467009581 467042349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21611)) 467042349 467075117 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467042349 467075117).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21611 467042349 467075117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21612)) 467075117 467107885 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467075117 467107885).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21612 467075117 467107885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21613)) 467107885 467140653 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 467107885 467140653).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21613 467107885 467140653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467009581 467075117).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 467009581 ≤ 467042349)
    (by decide : 467042349 ≤ 467075117) block0 block1

theorem join_0_1 : (twinPrimeSegment 467075117 467140653).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 467075117 ≤ 467107885)
    (by decide : 467107885 ≤ 467140653) block2 block3

theorem join_1_0 : (twinPrimeSegment 467009581 467140653).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 467009581 ≤ 467075117)
    (by decide : 467075117 ≤ 467140653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467009581 467140653).card = 433 := join_1_0

end S222C11
end Sude.GeneratedTwinScan
