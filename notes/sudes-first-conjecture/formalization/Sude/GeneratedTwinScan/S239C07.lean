import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22409)) 502136877 502169645 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 502136877 502169645).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22409 502136877 502169645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22409)) 502169645 502202413 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 502169645 502202413).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22409 502169645 502202413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22410)) 502202413 502235181 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 502202413 502235181).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22410 502202413 502235181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22411)) 502235181 502267949 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 502235181 502267949).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22411 502235181 502267949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 502136877 502202413).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 502136877 ≤ 502169645)
    (by decide : 502169645 ≤ 502202413) block0 block1

theorem join_0_1 : (twinPrimeSegment 502202413 502267949).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 502202413 ≤ 502235181)
    (by decide : 502235181 ≤ 502267949) block2 block3

theorem join_1_0 : (twinPrimeSegment 502136877 502267949).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 502136877 ≤ 502202413)
    (by decide : 502202413 ≤ 502267949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 502136877 502267949).card = 409 := join_1_0

end S239C07
end Sude.GeneratedTwinScan
